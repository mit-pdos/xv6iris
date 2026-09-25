(* PipeDisc.v -- THE PIPELINE APPLICATION'S PURE MODEL: the lines the user
   may type ([echo w1 .. wn] and [echo w1 .. wn | cat]), the alternative
   each round may take, and the console transcript the session calls for.
   Iris-free, over [EchoDisc]/[LineWords], so the claim can be read -- and
   refuted -- without opening the logic.

   Design of record: claude-notes/design/app-pipe.md section 1.  Worklist
   claude-notes/projects/app-pipe.md, lane PIPE-MODEL.

   WHAT THIS FILE IS.  [EchoDisc] models a session in which every round is
   one echo line.  Here a round is one of TWO line shapes, and the pipeline
   shape's round is run by THREE processes (the shell's runcmd child, echo
   at the pipe's write end and cat at its read end), so its console
   continuation has alternatives the echo line has not: the two exec
   diagnostics, EVERY BYTE-WISE INTERLEAVING of the two when both execs
   fail, and sh's own [pipe]/[fork] panics in the runcmd child.  Nothing
   survives the round -- a pipe dies with its era -- so the session
   function threads NO state and is [EchoDisc.sess] with a richer
   alternative type ([sessp]), read through an injective [nat] encoding so
   that the stage's [cs_auth]/[cs_lb] machinery is reused verbatim.
   Upstream's [FileDisc] is the shape this file copies, file section for
   file section; it is NOT imported (the two models share no statement).

   THE OBSERVER STILL CANNOT SEE WHICH ALTERNATIVE RAN, and does not need
   to: at [echo fork | cat] the good run prints "fork\n$ ", which is also
   what sh's [fork1] panic in the runcmd child prints.  So the determinacy
   theorem [sessp_prefix_det] -- the twin of [EchoOutPure.sess_prefix_det],
   which is what the stage spends -- concludes an equality of BYTES and
   never of indices.  Its engine is one observation, not a table: every
   alternative's own output is a '$'-free run followed by the prompt,
   except [PEcho 3] -- the MAIN loop's [fork1] panic, admitted at BOTH
   line shapes -- which kills the shell and re-enters init's prologue.

   WHERE THIS FILE DEPARTS FROM design section 1, each departure reported
   in claude-notes/projects/app-pipe.md under Findings.  The first two were
   RULED by the coordinator on 2026-09-18 and the ruling is what is landed;
   the rest are the lane's and stand.

   - [palt_ok] now admits [PEcho 3] -- and only [PEcho 3] among the
     [PEcho]s -- at an [LPipe] line.  Design section 1's table said
     "LEcho lines only" while its prose said "[LPipe] lines reach
     [alt_panic] exactly as [LEcho] lines do"; the lane reported that the
     table makes the theorem FALSE (the machine's MAIN-loop [fork1] can
     fail on a pipeline round, putting [alt_panic] and a FRESH PROLOGUE on
     the wire, which no other [LPipe] alternative prints) and the
     coordinator ruled for the prose.  See [palt_ok_pipe_panic],
     [palt_panic_3], and the transcript [demo_p_panic].
   - [palt_code] is POSITIONAL/BINARY, not [encode_nat]'s pairing:
     [PBoth sel] is [11 + 16 * bnum sel] where [bnum] reads [sel] as a
     binary numeral with a leading 1 (so leading [false]s survive), and
     [palt_of] divides.  The lane reported that [encode_nat] grows ~4x per
     entry, so a code at [|sel| = 33] was ~[4^33]; the binary reading is
     ~[2^34].  BUT [nat] IS UNARY, so even [2^34] is not computable --
     section 8 records the measured curve and says why the two [PBoth]
     demos are still proved by rewriting with [palt_of_code] rather than
     by [vm_compute].
   - [parse_pline] inverts [line_body] (the body [LineWords.bodies_of]
     cuts), NOT [line_bytes] (which carries the closing newline the cut
     has already stripped).  The brief's
     [parse_pline (line_body (line_bytes l)) = Some l] is not even
     well-typed; the law that holds is [parse_pline_body] below, and
     [line_bytes l = line_body l ++ [wl_nl]] is kept as its own equation.
     This is [FileDisc]'s first departure, verbatim.
   - [pcont_shape] gives only "a '$'-free run, then the prompt", and
     [pcont_shape_nl] gives [FileDisc.cont_shape]'s stronger reading as a
     DISJUNCTION: the run's only newline is its last byte, OR the run opens
     on 'e'.  The newline half is FALSE at [PBoth sel]
     ([pcont_both_no_nl_shape] below): a merge of the two diagnostics
     carries TWO newlines.  The second arm replaces it, and it is all the
     determinacy proof wants, because the only comparison that spends the
     lemma puts sh's panic line -- which opens on 'f' -- on the other side
     ([pd_head_ne_panic]).
   - [pmerge]'s inverse law wants a STOPPING merge, not a skipping one:
     with "a [true] at an exhausted [d1] consumes the selector and
     produces nothing" the law [pmerge_take] is false (see the comment at
     [pmerge]).  Landed stopping, which makes [pmerge_take] and hence
     [pmerge_prefix] unconditional.  (The name is [pmerge] and not [merge]
     so as not to shadow stdpp's map [merge], which lane PIPE-2W will
     import beside this file.)
   - [pipe_phi] takes the history alone, as [FileDisc.file_phi] does; the
     [gstate] argument [AppEcho.echo_phi] carries is the record's, and
     lane PIPE-STAGE adds it. *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [obs_wire Uart0], [cycles_of] *)
Require Import LineWords.        (* the word line and the parser *)
Require Import EchoDisc.         (* the console discipline this one extends *)
Require Export LineBytes.        (* [nodollar], the byte facts every model reads *)
Require Import LineModel.        (* the line model this one instantiates *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  1.  THE LINES THE USER MAY TYPE                                        *)
(* ====================================================================== *)

(* sh's lexer sees '|' as a symbol token; the pipeline is CANONICAL -- one
   blank each side, and the right-hand command is the single word [cat]
   with NO argument, so cat reads its standard input.  That is the shape
   the sh walk (design section 5.1) is stated at. *)
Definition suf_pipecat : list (bv 8) := sb " | cat"%string.

Inductive pline :=
  | LEcho (ws : list (list (bv 8)))
  | LPipe (ws : list (list (bv 8))).

Global Instance pline_eq_dec : EqDecision pline.
Proof using. solve_decision. Defined.
Global Instance pline_inhabited : Inhabited pline := populate (LEcho []).

Definition pline_ws (l : pline) : list (list (bv 8)) :=
  match l with LEcho ws => ws | LPipe ws => ws end.

(* the line's SHAPE, which is what discipline rule D4 is guarded on *)
Definition pline_is_pipe (l : pline) : bool :=
  match l with LEcho _ => false | LPipe _ => true end.

(* THE BODY the console cut keeps, and the LINE the user typed: the body
   and the newline [gets] stops at.  [line_bytes (LEcho ws)] is
   [LineWords.wl_line ws] on the nose. *)
Definition line_body (l : pline) : list (bv 8) :=
  match l with
  | LEcho ws => wl_body ws
  | LPipe ws => wl_body ws ++ suf_pipecat
  end.

Definition line_bytes (l : pline) : list (bv 8) := line_body l ++ [wl_nl].

Lemma line_bytes_echo ws : line_bytes (LEcho ws) = wl_line ws.
Proof using. reflexivity. Qed.

Lemma line_bytes_body l : line_bytes l = line_body l ++ [wl_nl].
Proof using. reflexivity. Qed.

Definition pline_ok (l : pline) : Prop :=
  match l with
  | LEcho ws => line_ok ws
  | LPipe ws => line_ok ws /\ (length (line_bytes (LPipe ws)) < line_max)%nat
  end.

Global Instance pline_ok_dec l : Decision (pline_ok l).
Proof using. destruct l; rewrite /pline_ok; apply _. Defined.

Lemma pline_ok_ws l : pline_ok l -> line_ok (pline_ws l).
Proof using. destruct l as [ws | ws]; [exact id | by intros [H _]]. Qed.

(* ---- the pipe symbol, and the bytes a line body may carry ------------ *)

Definition wl_bar : bv 8 := Z_to_bv 8 124%Z.

(* the partial line the user is in the middle of.  '|' is not a
   [wl_body_byte] and the line [echo hi | cat] passes through the input
   [echo hi |], so the pipeline application's D3 admits it. *)
Definition pbody_byte (b : bv 8) : Prop := wl_body_byte b \/ b = wl_bar.

Global Instance pbody_byte_dec b : Decision (pbody_byte b).
Proof using. rewrite /pbody_byte. apply _. Defined.

Lemma pbody_byte_of_body b : wl_body_byte b -> pbody_byte b.
Proof using. by left. Qed.

Lemma suf_pipecat_len : length suf_pipecat = 6%nat.
Proof using. by vm_compute. Qed.

Lemma suf_pipecat_bytes : Forall pbody_byte suf_pipecat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_bar_not_body : ~ wl_body_byte wl_bar.
Proof using.
  rewrite /wl_body_byte /wl_alnum /wl_bar. intros [H | H].
  - assert (Hv : bv_unsigned (Z_to_bv 8 124%Z) = 124%Z) by (by vm_compute). lia.
  - apply (f_equal bv_unsigned) in H. rewrite wl_sp_val in H.
    assert (Hv : bv_unsigned (Z_to_bv 8 124%Z) = 124%Z) by (by vm_compute). lia.
Qed.

Lemma suf_pipecat_bar : wl_bar ∈ suf_pipecat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- THE PARSER ------------------------------------------------------ *)

Definition strip_pipecat (b : list (bv 8)) : option (list (bv 8)) :=
  if decide (suf_pipecat `suffix_of` b)
  then Some (take (length b - length suf_pipecat) b) else None.

Lemma strip_pipecat_app c : strip_pipecat (c ++ suf_pipecat) = Some c.
Proof using.
  rewrite /strip_pipecat decide_True; [| by exists c].
  rewrite length_app.
  replace (length c + length suf_pipecat - length suf_pipecat)%nat
    with (length c) by lia.
  by rewrite take_app_length.
Qed.

Lemma strip_pipecat_Some b c : strip_pipecat b = Some c -> b = c ++ suf_pipecat.
Proof using.
  intros Hc. destruct (decide (suf_pipecat `suffix_of` b)) as [[k ->] | Hn].
  - rewrite (strip_pipecat_app k) in Hc. by injection Hc as <-.
  - rewrite /strip_pipecat decide_False in Hc; [discriminate | exact Hn].
Qed.

Lemma strip_pipecat_None b c : strip_pipecat b = None -> b <> c ++ suf_pipecat.
Proof using. intros H ->. by rewrite strip_pipecat_app in H. Qed.

(* THE PARSE of one body.  It answers [Some] only for an ADMISSIBLE line,
   so [is_Some (parse_pline b)] IS the content half of the discipline at
   that body; and what it answers determines the body
   ([line_body_parse]). *)
Definition parse_pline (b : list (bv 8)) : option pline :=
  match strip_pipecat b with
  | Some c =>
      if decide (body_ok c /\ (S (length b) < line_max)%nat)
      then Some (LPipe (wl_words c)) else None
  | None => if decide (body_ok b) then Some (LEcho (wl_words b)) else None
  end.

Definition pline_of (b : list (bv 8)) : pline :=
  default inhabitant (parse_pline b).

(* the lines of a body list, in order *)
Definition plines_of (I : list (bv 8)) : list pline := pline_of <$> bodies_of I.

Lemma parse_pline_ok b l : parse_pline b = Some l -> pline_ok l.
Proof using.
  rewrite /parse_pline. destruct (strip_pipecat b) as [c |] eqn:Hs.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [[Hbody Hok] Hlen]. rewrite /pline_ok. split.
    + exact Hok.
    + pose proof (strip_pipecat_Some b c Hs) as Hbc.
      rewrite Hbc length_app in Hlen.
      rewrite /line_bytes /line_body !length_app Hbody.
      cbn [length] in Hlen |- *. lia.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [Hbody Hok]. exact Hok.
Qed.

Lemma line_body_parse b l : parse_pline b = Some l -> b = line_body l.
Proof using.
  rewrite /parse_pline. destruct (strip_pipecat b) as [c |] eqn:Hs.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [[Hbody _] _]. rewrite /line_body Hbody.
    exact (strip_pipecat_Some b c Hs).
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [Hbody _]. by rewrite /line_body Hbody.
Qed.

(* ...AND THE LINE'S OWN BYTES, which is the form the shell's read link
   hands back: what the user typed is the body plus its newline. *)
Lemma line_bytes_parse b l :
  parse_pline b = Some l -> line_bytes l = b ++ [wl_nl].
Proof using. intro H. by rewrite /line_bytes -(line_body_parse b l H). Qed.

(* ---- ...AND ITS INVERSE ---------------------------------------------- *)

Lemma body_no_pipecat ws (c : list (bv 8)) :
  line_ok ws -> wl_body ws <> c ++ suf_pipecat.
Proof using.
  intros Hok Heq.
  pose proof (wl_body_bytes ws (line_ok_wf _ Hok)) as Hfb.
  rewrite Heq in Hfb. apply Forall_app in Hfb as [_ Hsuf].
  exact (wl_bar_not_body
           (proj1 (Forall_forall _ _) Hsuf wl_bar suf_pipecat_bar)).
Qed.

Lemma parse_pline_body l : pline_ok l -> parse_pline (line_body l) = Some l.
Proof using.
  destruct l as [ws | ws].
  - (* LEcho *)
    intro Hok. rewrite /line_body /parse_pline.
    destruct (strip_pipecat (wl_body ws)) as [c |] eqn:Hs.
    { exfalso. exact (body_no_pipecat ws c Hok (strip_pipecat_Some _ _ Hs)). }
    rewrite decide_True; last first.
    { rewrite /body_ok (wl_words_body ws (line_ok_wf _ Hok)).
      split; [reflexivity | exact Hok]. }
    by rewrite (wl_words_body ws (line_ok_wf _ Hok)).
  - (* LPipe *)
    intros [Hok Hlen]. rewrite /line_body /parse_pline.
    rewrite strip_pipecat_app decide_True; last first.
    { split.
      - rewrite /body_ok (wl_words_body ws (line_ok_wf _ Hok)).
        split; [reflexivity | exact Hok].
      - rewrite /line_bytes /line_body !length_app in Hlen.
        cbn [length] in Hlen. rewrite length_app. lia. }
    by rewrite (wl_words_body ws (line_ok_wf _ Hok)).
Qed.

Lemma pline_of_body l : pline_ok l -> pline_of (line_body l) = l.
Proof using. intro H. by rewrite /pline_of (parse_pline_body l H). Qed.

(* ---- D3 FOR THE PIPELINE APPLICATION --------------------------------- *)

Definition pbody_ok (b : list (bv 8)) : Prop := is_Some (parse_pline b).

Global Instance pbody_ok_dec b : Decision (pbody_ok b).
Proof using. rewrite /pbody_ok. apply _. Defined.

Lemma pbody_ok_line b :
  pbody_ok b -> pline_ok (pline_of b) /\ b = line_body (pline_of b).
Proof using.
  intros [l Hl]. rewrite /pline_of Hl /=.
  split; [exact (parse_pline_ok b l Hl) | exact (line_body_parse b l Hl)].
Qed.

Lemma pbody_ok_of l : pline_ok l -> pbody_ok (line_body l).
Proof using. intro H. exists l. exact (parse_pline_body l H). Qed.

Lemma pbody_ok_bytes b : pbody_ok b -> Forall pbody_byte b.
Proof using.
  intro Hb. destruct (pbody_ok_line b Hb) as [Hok Heq]. rewrite Heq.
  destruct (pline_of b) as [ws | ws]; rewrite /line_body.
  - apply Forall_impl with (P := wl_body_byte);
      [exact (wl_body_bytes ws (line_ok_wf _ Hok)) | exact pbody_byte_of_body].
  - apply Forall_app. split; [| exact suf_pipecat_bytes].
    destruct Hok as [Hok _].
    apply Forall_impl with (P := wl_body_byte);
      [exact (wl_body_bytes ws (line_ok_wf _ Hok)) | exact pbody_byte_of_body].
Qed.

Lemma pbody_ok_short b : pbody_ok b -> (S (length b) < line_max)%nat.
Proof using.
  intro Hb. destruct (pbody_ok_line b Hb) as [Hok Heq]. rewrite Heq.
  destruct (pline_of b) as [ws | ws].
  - pose proof (line_ok_len ws Hok) as Hl.
    rewrite wl_line_length in Hl. rewrite /line_body. lia.
  - destruct Hok as [_ Hl].
    rewrite /line_bytes /line_body length_app in Hl. cbn [length] in Hl.
    rewrite /line_body. lia.
Qed.

(* D3: every COMPLETE body parses to an admissible line, and the partial
   line is body bytes -- '|' included -- short enough that its newline
   still fits [getcmd]'s buffer. *)
Definition disc_input_p (I : list (bv 8)) : Prop :=
  Forall pbody_ok (bodies_of I)
  /\ Forall pbody_byte (rest_of I)
  /\ (S (length (rest_of I)) < line_max)%nat.

Global Instance disc_input_p_dec I : Decision (disc_input_p I).
Proof using. rewrite /disc_input_p. apply _. Defined.

Lemma disc_input_p_nil : disc_input_p [].
Proof using.
  rewrite /disc_input_p bodies_of_nil rest_of_nil /line_max.
  split; [constructor |]. split; [constructor | cbn [length]; lia].
Qed.

Lemma disc_input_p_snoc I b : disc_input_p (I ++ [b]) -> disc_input_p I.
Proof using.
  intros (Hb & Hr & Hs). destruct (decide (b = wl_nl)) as [-> | Hne].
  - rewrite bodies_of_snoc_nl in Hb.
    apply Forall_app in Hb as [Hb1 Hb2]. rewrite Forall_singleton in Hb2.
    split; [exact Hb1 |]. split; [exact (pbody_ok_bytes _ Hb2) |].
    exact (pbody_ok_short _ Hb2).
  - rewrite (bodies_of_snoc_other I b Hne) in Hb.
    rewrite (rest_of_snoc_other I b Hne) in Hr, Hs.
    apply Forall_app in Hr as [Hr1 _].
    split; [exact Hb |]. split; [exact Hr1 |].
    rewrite (length_app (rest_of I) [b]) in Hs. cbn [length] in Hs. lia.
Qed.

Lemma disc_input_p_prefix I I' :
  I `prefix_of` I' -> disc_input_p I' -> disc_input_p I.
Proof using.
  intros [k ->]. induction k as [| b k IH] using rev_ind; intro Hd.
  - by rewrite app_nil_r in Hd.
  - apply IH. rewrite app_assoc in Hd. exact (disc_input_p_snoc _ _ Hd).
Qed.

Lemma disc_input_p_body I i b :
  disc_input_p I -> bodies_of I !! i = Some b -> pbody_ok b.
Proof using. intros (Hb & _ & _) Hi. exact (Forall_lookup_1 _ _ _ _ Hb Hi). Qed.

Lemma disc_input_p_line I i b :
  disc_input_p I -> bodies_of I !! i = Some b ->
  pline_ok (pline_of b) /\ b = line_body (pline_of b).
Proof using.
  intros Hd Hi. exact (pbody_ok_line b (disc_input_p_body I i b Hd Hi)).
Qed.

Lemma disc_input_p_rest_short I :
  disc_input_p I -> (S (length (rest_of I)) < line_max)%nat.
Proof using. by intros (_ & _ & H). Qed.

Lemma disc_input_p_at I i :
  disc_input_p I -> (i < nlines I)%nat ->
  pline_ok (pline_of (bodies_of I !!! i))
  /\ bodies_of I !!! i = line_body (pline_of (bodies_of I !!! i)).
Proof using.
  intros Hd Hi. rewrite /nlines in Hi.
  destruct (lookup_lt_is_Some_2 (bodies_of I) i Hi) as [b Hb].
  rewrite (list_lookup_total_correct _ _ _ Hb).
  exact (pbody_ok_line b (disc_input_p_body I i b Hd Hb)).
Qed.

(* ---- AN ECHO-DISCIPLINED INPUT IS PIPE-DISCIPLINED -------------------- *)
(* [EchoDisc]'s lines are this model's [LEcho] lines, so nothing about the
   echo application's discipline is weakened or restated. *)

Lemma parse_pline_echo b : body_ok b -> parse_pline b = Some (LEcho (wl_words b)).
Proof using.
  intro Hb. rewrite /parse_pline.
  destruct (strip_pipecat b) as [c |] eqn:Hs.
  { exfalso. pose proof (strip_pipecat_Some b c Hs) as Hbc.
    pose proof (body_ok_bytes b Hb) as Hfb.
    rewrite Hbc in Hfb. apply Forall_app in Hfb as [_ Hsuf].
    exact (wl_bar_not_body
             (proj1 (Forall_forall _ _) Hsuf wl_bar suf_pipecat_bar)). }
  rewrite decide_True; [reflexivity | exact Hb].
Qed.

Lemma pline_of_echo b : body_ok b -> pline_of b = LEcho (wl_words b).
Proof using. intro H. by rewrite /pline_of (parse_pline_echo b H). Qed.

Lemma pbody_ok_of_body b : body_ok b -> pbody_ok b.
Proof using.
  intro H. exists (LEcho (wl_words b)). exact (parse_pline_echo b H).
Qed.

Lemma disc_input_p_of_disc_input I : disc_input I -> disc_input_p I.
Proof using.
  intros (Hb & Hr & Hs). split.
  { apply Forall_impl with (P := body_ok); [exact Hb | exact pbody_ok_of_body]. }
  split; [| exact Hs].
  apply Forall_impl with (P := wl_body_byte);
    [exact Hr | exact pbody_byte_of_body].
Qed.

(* ====================================================================== *)
(*  2.  THE DIAGNOSTICS, AND THE MERGE OF TWO OF THEM                      *)
(* ====================================================================== *)

(* SH'S DIAGNOSTICS ARE WORD LINES, as [EchoDisc.dg_exec] is.  The two exec
   diagnostics are ONE [fprintf(2, "exec %s failed\n", argv[0])]
   (user/sh.c:80) at the two commands of the pipeline; the two panics are
   [panic("pipe")] (user/sh.c:47) and [panic("fork")] (user/sh.c:194),
   whose printer is [fprintf(2, "%s\n", s)] (user/sh.c:181).  Stating them
   in the word vocabulary is what makes their collision with an echoed
   line a statement the parse settles. *)
Definition dg_exec_cat : list (list (bv 8)) :=
  [ sb "exec"%string; sb "cat"%string; sb "failed"%string ].
Definition dg_pipe : list (list (bv 8)) := [ sb "pipe"%string ].

Lemma dg_exec_cat_line :
  wl_line dg_exec_cat = sb "exec cat failed"%string ++ nlb.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma dg_pipe_line : wl_line dg_pipe = sb "pipe"%string ++ nlb.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* THE TWO DIAGNOSTICS THAT CAN COLLIDE ON THE WIRE, as raw bytes: the
   left child's (echo could not be exec'd) and the right child's (cat
   could not be).  [dg_execL] is [EchoDisc.dg_exec]'s line on the nose,
   which is why an [LEcho] round and an [LPipe] round print the SAME bytes
   when their left exec fails. *)
Definition dg_execL : list (bv 8) := wl_line dg_exec.
Definition dg_execR : list (bv 8) := wl_line dg_exec_cat.

Lemma dg_execL_string : dg_execL = sb "exec echo failed"%string ++ nlb.
Proof using. exact dg_exec_line. Qed.

Lemma dg_execR_string : dg_execR = sb "exec cat failed"%string ++ nlb.
Proof using. exact dg_exec_cat_line. Qed.

Lemma dg_execL_len : length dg_execL = 17%nat.
Proof using. by vm_compute. Qed.

Lemma dg_execR_len : length dg_execR = 16%nat.
Proof using. by vm_compute. Qed.

(* ---- THE ROUND'S FOUR CONSTANT CONTINUATIONS ------------------------- *)

Definition alt_execL : list (bv 8) := dg_execL ++ u_prompt.
Definition alt_execR : list (bv 8) := dg_execR ++ u_prompt.
Definition alt_pipe  : list (bv 8) := wl_line dg_pipe ++ u_prompt.
Definition alt_forkc : list (bv 8) := wl_line dg_fork ++ u_prompt.

(* [alt_execL] IS the echo application's exec alternative: one [fprintf],
   one format, one argument. *)
Lemma alt_execL_echo : alt_execL = alt_execfail.
Proof using. reflexivity. Qed.

Lemma alt_execL_string :
  alt_execL = sb "exec echo failed"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma alt_execR_string :
  alt_execR = sb "exec cat failed"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma alt_pipe_string :
  alt_pipe = sb "pipe"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* THE RUNCMD CHILD'S FORK PANIC ENDS IN THE PROMPT and the MAIN LOOP'S
   DOES NOT.  [panic] in the runcmd child exits the CHILD, the parent
   shell's [wait(0)] returns and it prints the next prompt
   ([alt_forkc]); the main loop's own [fork1] kills the SHELL, init reaps
   it and re-enters the prologue ([EchoDisc.alt_panic], with no prompt).
   The two are the same four bytes followed by different things, which is
   exactly why the model needs both. *)
Lemma alt_forkc_panic : alt_forkc = alt_panic ++ u_prompt.
Proof using. reflexivity. Qed.

Lemma alt_forkc_len : length alt_forkc = 7%nat.
Proof using. by vm_compute. Qed.

Lemma alt_forkc_string :
  alt_forkc = sb "fork"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- '$' IS THE ONE BYTE ONLY THE PROMPT CARRIES --------------------- *)


(* '$' is not a byte of any word line, and a word line's ONE newline is
   its last byte.  Both readings come off [LineWords] at once. *)
Lemma pd_wl_line_shape ws :
  wl_wf ws ->
  Forall nodollar (wl_line ws)
  /\ exists v, wl_nl ∉ v /\ wl_line ws = v ++ [wl_nl].
Proof using.
  intro Hwf. split.
  - apply Forall_forall. intros b Hb.
    pose proof (wl_line_byte_val ws b Hwf Hb) as Hv. rewrite /nodollar. lia.
  - exists (wl_body ws). split; [exact (wl_body_nonl ws Hwf) | reflexivity].
Qed.

Lemma pd_wl_line_shape' ws :
  wl_wf ws ->
  Forall nodollar (wl_line ws)
  /\ (wl_nl ∉ wl_line ws
      \/ exists v, wl_nl ∉ v /\ wl_line ws = v ++ [wl_nl]).
Proof using.
  intro H. destruct (pd_wl_line_shape ws H) as [H1 H2].
  split; [exact H1 | by right].
Qed.

(* ---- THE MERGE: TWO WRITERS ON ONE WIRE ------------------------------ *)

(* HOW MANY BYTES OF THE LEFT DIAGNOSTIC AN INTERLEAVING SELECTS *)
Fixpoint count_true (sel : list bool) : nat :=
  match sel with
  | [] => 0%nat
  | true :: s => S (count_true s)
  | false :: s => count_true s
  end.

Lemma count_true_le sel : (count_true sel <= length sel)%nat.
Proof using.
  induction sel as [| [|] s IH]; cbn [count_true length]; lia.
Qed.

Lemma count_true_app s1 s2 :
  count_true (s1 ++ s2) = (count_true s1 + count_true s2)%nat.
Proof using.
  induction s1 as [| [|] s IH]; cbn [app count_true]; lia.
Qed.

Lemma count_true_replicate_true n : count_true (replicate n true) = n.
Proof using. induction n as [| n IH]; cbn [replicate count_true]; lia. Qed.

Lemma count_true_replicate_false n : count_true (replicate n false) = 0%nat.
Proof using. induction n as [| n IH]; cbn [replicate count_true]; lia. Qed.

(* THE INTERLEAVING [sel] PUTS ON THE WIRE, one byte per selector entry:
   [true] takes the next byte of [d1], [false] the next byte of [d2].

   IT STOPS AT AN EXHAUSTED SIDE and does not skip.  The skipping variant
   ("a [true] at an empty [d1] consumes the selector and produces
   nothing") makes [pmerge_take] FALSE -- at [sel = [true; false]],
   [d1 = []], [d2 = [x]] it gives [pmerge sel d1 d2 = [x]] while
   [pmerge (take 1 sel) d1 d2 = []], so a prefix of a pmerge would not be a
   pmerge of a prefix of the selector, and [pmerge_prefix] (which design
   section 4.3 spends) would need side conditions.  Stopping makes both
   laws UNCONDITIONAL, and at every [sel] the model admits ([palt_ok]'s
   length and count conditions) the two definitions agree. *)
Fixpoint pmerge (sel : list bool) (d1 d2 : list (bv 8)) : list (bv 8) :=
  match sel with
  | [] => []
  | true :: s =>
      match d1 with [] => [] | b :: d1' => b :: pmerge s d1' d2 end
  | false :: s =>
      match d2 with [] => [] | b :: d2' => b :: pmerge s d1 d2' end
  end.

Lemma pmerge_nil_sel d1 d2 : pmerge [] d1 d2 = [].
Proof using. reflexivity. Qed.

Lemma pmerge_true_cons s b d1 d2 :
  pmerge (true :: s) (b :: d1) d2 = b :: pmerge s d1 d2.
Proof using. reflexivity. Qed.

Lemma pmerge_false_cons s d1 b d2 :
  pmerge (false :: s) d1 (b :: d2) = b :: pmerge s d1 d2.
Proof using. reflexivity. Qed.

Lemma pmerge_true_nil s d2 : pmerge (true :: s) [] d2 = [].
Proof using. reflexivity. Qed.

Lemma pmerge_false_nil s d1 : pmerge (false :: s) d1 [] = [].
Proof using. reflexivity. Qed.

(* the pmerge is as long as the selector, once both sides have the bytes *)
Lemma pmerge_length sel d1 d2 :
  (count_true sel <= length d1)%nat ->
  (length sel - count_true sel <= length d2)%nat ->
  length (pmerge sel d1 d2) = length sel.
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 H1 H2; [done | |].
  - pose proof (count_true_le s) as Hcl.
    cbn [count_true length] in H1, H2.
    destruct d1 as [| b d1']; [cbn [length] in H1; lia |].
    rewrite pmerge_true_cons. cbn [length]. rewrite IH; [lia | |];
      cbn [length] in H1 |- *; lia.
  - pose proof (count_true_le s) as Hcl.
    cbn [count_true length] in H1, H2.
    destruct d2 as [| b d2']; [cbn [length] in H2; lia |].
    rewrite pmerge_false_cons. cbn [length]. rewrite IH; [lia | |];
      cbn [length] in H2 |- *; lia.
Qed.

(* A PREFIX OF A MERGE IS A MERGE OF A PREFIX OF THE SELECTOR.  This is
   the engine of the inverse law, and it is unconditional. *)
Lemma pmerge_take sel d1 d2 k :
  take k (pmerge sel d1 d2) = pmerge (take k sel) d1 d2.
Proof using.
  revert d1 d2 k. induction sel as [| [|] s IH]; intros d1 d2 k.
  - by rewrite !take_nil.
  - destruct k as [| k']; [by rewrite !take_0 |].
    destruct d1 as [| b d1']; [by cbn |].
    cbn. by rewrite IH.
  - destruct k as [| k']; [by rewrite !take_0 |].
    destruct d2 as [| b d2']; [by cbn |].
    cbn. by rewrite IH.
Qed.

(* ...and the pmerge reads only as much of each side as the selector asks
   for, which turns a prefix of the selector into a pair of cursors *)
Lemma pmerge_take_lr sel d1 d2 c1 c2 :
  (count_true sel <= c1)%nat -> (length sel - count_true sel <= c2)%nat ->
  pmerge sel (take c1 d1) (take c2 d2) = pmerge sel d1 d2.
Proof using.
  revert d1 d2 c1 c2. induction sel as [| [|] s IH]; intros d1 d2 c1 c2 H1 H2;
    [done | |].
  - pose proof (count_true_le s) as Hcl.
    cbn [count_true length] in H1, H2.
    destruct c1 as [| c1']; [lia |].
    destruct d1 as [| b d1']; [by rewrite take_nil |].
    rewrite (_ : take (S c1') (b :: d1') = b :: take c1' d1');
      [| reflexivity].
    rewrite !pmerge_true_cons. f_equal. apply IH; lia.
  - pose proof (count_true_le s) as Hcl.
    cbn [count_true length] in H1, H2.
    destruct c2 as [| c2']; [lia |].
    destruct d2 as [| b d2']; [by rewrite take_nil |].
    rewrite (_ : take (S c2') (b :: d2') = b :: take c2' d2');
      [| reflexivity].
    rewrite !pmerge_false_cons. f_equal. apply IH; lia.
Qed.

(* DESIGN SECTION 4.3'S LAW: a prefix of a pmerge is a pmerge of prefixes --
   the two writers' cursors are [c1] and [c2] and the interleaving so far
   is [sel'], a prefix of the round's. *)
Lemma pmerge_prefix_take (sel : list bool) (d1 d2 : list (bv 8)) (k : nat) :
  take k (pmerge sel d1 d2)
  = pmerge (take k sel) (take (count_true (take k sel)) d1)
          (take (length (take k sel) - count_true (take k sel))%nat d2).
Proof using.
  rewrite pmerge_take. symmetry. apply pmerge_take_lr; lia.
Qed.

Lemma pmerge_prefix (sel : list bool) (d1 d2 p : list (bv 8)) :
  p `prefix_of` pmerge sel d1 d2 ->
  exists (sel' : list bool) (c1 c2 : nat),
    p = pmerge sel' (take c1 d1) (take c2 d2) /\ sel' `prefix_of` sel.
Proof using.
  intros [z Hz].
  exists (take (length p) sel), (count_true (take (length p) sel)),
         (length (take (length p) sel)
          - count_true (take (length p) sel))%nat.
  split; [| apply prefix_take].
  rewrite -pmerge_prefix_take Hz. by rewrite take_app_length.
Qed.

(* NEITHER DIAGNOSTIC CARRIES A '$', so no interleaving of them does --
   which is what puts every [PBoth] round under the same reading as every
   other non-panic round (section 4). *)
Lemma pmerge_nodollar sel d1 d2 :
  Forall nodollar d1 -> Forall nodollar d2 ->
  Forall nodollar (pmerge sel d1 d2).
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 H1 H2;
    [constructor | |].
  - destruct d1 as [| b d1']; [by constructor |].
    apply Forall_cons_1 in H1 as [Hb H1].
    rewrite pmerge_true_cons. apply Forall_cons. split; [exact Hb | by apply IH].
  - destruct d2 as [| b d2']; [by constructor |].
    apply Forall_cons_1 in H2 as [Hb H2].
    rewrite pmerge_false_cons. apply Forall_cons. split; [exact Hb | by apply IH].
Qed.

Lemma dg_execL_nodollar : Forall nodollar dg_execL.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma dg_execR_nodollar : Forall nodollar dg_execR.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma pmerge_no_dollar sel : Forall nodollar (pmerge sel dg_execL dg_execR).
Proof using.
  apply pmerge_nodollar; [exact dg_execL_nodollar | exact dg_execR_nodollar].
Qed.

(* the first byte of a pmerge is the first byte of one of the two sides --
   the one reading the negative witness (section 8) spends *)
Lemma pmerge_head sel d1 d2 (b : bv 8) :
  pmerge sel d1 d2 !! 0%nat = Some b ->
  d1 !! 0%nat = Some b \/ d2 !! 0%nat = Some b.
Proof using.
  destruct sel as [| [|] s]; [discriminate | |].
  - destruct d1 as [| c d1']; [discriminate |].
    rewrite pmerge_true_cons. cbn. intros [= <-]. by left.
  - destruct d2 as [| c d2']; [discriminate |].
    rewrite pmerge_false_cons. cbn. intros [= <-]. by right.
Qed.

(* THE ALL-[false] SELECTOR reads the RIGHT source alone, which is the
   terminal round that got no stray byte ([pcont_forkS_old]). *)
Lemma pmerge_all_false_gen (n : nat) (d1 d2 : list (bv 8)) :
  pmerge (replicate n false) d1 d2 = take n d2.
Proof using.
  revert d1 d2. induction n as [| n IH]; intros d1 d2; [reflexivity |].
  cbn [replicate]. destruct d2 as [| b d2'].
  - by rewrite pmerge_false_nil take_nil.
  - rewrite pmerge_false_cons. cbn [take]. by rewrite IH.
Qed.

(* ---- IS THIS RUN A SHUFFLE OF THE TWO FORK-ROUND SOURCES? ------------ *)

(* THE TEST THE TERMINAL ROUND IS READ BY (lane PIPE-MODEL-3, design
   section 4.3h).  A pipeline round whose [fork1] failed has TWO live
   writers -- the runcmd child and sh's main loop between them write
   [alt_forkc] ("fork\n$ "), and the STRAY left child, whose own exec
   failed, writes a prefix of [dg_execL] at any time, including after the
   prompt.  So the round's bytes are a shuffle of the two lists, and
   [shufb] is that test, by recursion on the run: at each byte, take it
   from the left source or from the right one.  It PRUNES at the first
   byte that matches neither, which is why it evaluates in milliseconds
   on the demos below even though its worst case is exponential.

   [pmergeable] is the test and not the existential [exists sel, ...] on
   purpose: it is decidable and [vm_compute]-able BY CONSTRUCTION, which
   is what discipline rule D4 and the decision procedure of
   [PipeDiscDec] both need, and what no statement about [sel] can be --
   an admitted [sel] here has length up to 24. *)
Fixpoint shufb (u d1 d2 : list (bv 8)) : bool :=
  match u with
  | [] => true
  | x :: u' =>
      (match d1 with
       | y :: d1' => bool_decide (y = x) && shufb u' d1' d2
       | [] => false
       end)
      || (match d2 with
          | y :: d2' => bool_decide (y = x) && shufb u' d1 d2'
          | [] => false
          end)
  end.

Definition pmergeable (u : list (bv 8)) : Prop :=
  shufb u dg_execL alt_forkc = true.

Global Instance pmergeable_dec u : Decision (pmergeable u).
Proof using. rewrite /pmergeable. apply _. Defined.

Lemma pmergeable_nil : pmergeable [].
Proof using. reflexivity. Qed.

(* A PREFIX OF A SHUFFLE IS A SHUFFLE -- take the same choices.  This is
   the one closure law [pcont_pair_det] spends: the claim's terminal block
   is a shuffle, so anything the discipline reads BELOW it is one too. *)
Lemma shufb_prefix (u' u d1 d2 : list (bv 8)) :
  u' `prefix_of` u -> shufb u d1 d2 = true -> shufb u' d1 d2 = true.
Proof using.
  revert u d1 d2. induction u' as [| x u' IH]; intros u d1 d2 Hp Hs;
    [reflexivity |].
  destruct u as [| y u]; [by apply prefix_nil_not in Hp |].
  apply prefix_cons_inv_1 in Hp as Hxy.
  apply prefix_cons_inv_2 in Hp as Hpr.
  subst y. cbn [shufb] in Hs |- *.
  apply orb_prop in Hs as [Hs | Hs].
  - destruct d1 as [| z d1']; [discriminate |].
    apply andb_prop in Hs as [Hz Hs].
    rewrite Hz (IH u d1' d2 Hpr Hs). reflexivity.
  - destruct d2 as [| z d2']; [discriminate |].
    apply andb_prop in Hs as [Hz Hs].
    rewrite Hz (IH u d1 d2' Hpr Hs) orb_true_r. reflexivity.
Qed.

Lemma pmergeable_prefix (u' u : list (bv 8)) :
  u' `prefix_of` u -> pmergeable u -> pmergeable u'.
Proof using. rewrite /pmergeable. apply shufb_prefix. Qed.

(* ...AND A MERGE IS ONE, which is what makes the test COMPLETE for the
   blocks the terminal round can write. *)
Lemma shufb_pmerge (sel : list bool) (d1 d2 : list (bv 8)) :
  (count_true sel <= length d1)%nat ->
  (length sel - count_true sel <= length d2)%nat ->
  shufb (pmerge sel d1 d2) d1 d2 = true.
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 H1 H2;
    [reflexivity | |].
  - cbn [count_true length] in H1, H2.
    destruct d1 as [| y d1']; [cbn [length] in H1; lia |].
    rewrite pmerge_true_cons. cbn [shufb].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    rewrite (IH d1' d2 ltac:(cbn [length] in H1; lia) ltac:(lia)).
    reflexivity.
  - cbn [count_true length] in H1, H2.
    pose proof (count_true_le s) as Hle.
    destruct d2 as [| y d2']; [cbn [length] in H2; lia |].
    rewrite pmerge_false_cons. cbn [shufb].
    rewrite bool_decide_eq_true_2; [| reflexivity].
    rewrite (IH d1 d2' ltac:(lia) ltac:(cbn [length] in H2; lia)).
    by rewrite orb_true_r.
Qed.

(* ====================================================================== *)
(*  3.  THE ROUND'S ALTERNATIVES                                           *)
(* ====================================================================== *)

(* ONE ALTERNATIVE DECIDES A ROUND: what the console shows.  [PEcho] is the
   echo application's four, unchanged; the rest are the pipeline line's,
   and design section 1 is the table:

     PEcho a     the echo application's four ([EchoDisc.line_alts_of])
     PRan        wl_line (drop 1 ws) ++ "$ "       the line, then the prompt
     PExecL      "exec echo failed\n$ "            left exec failed; cat
                                                   printed nothing (EOF at
                                                   an empty pipe)
     PExecR      "exec cat failed\n$ "             right exec failed; echo's
                                                   bytes went into the pipe
                                                   and stayed there
     PBoth sel   pmerge sel dg_execL dg_execR ++ "$ "
                                                   both failed; [sel] is the
                                                   byte-wise interleaving
     PPipe       "pipe\n$ "                        pipe(2) failed; sh's panic
                                                   in the runcmd CHILD
     PForkS sel  pmerge sel dg_execL alt_forkc     a fork1 failed in the
                                                   runcmd child; [sel] is
                                                   the byte-wise
                                                   interleaving of the
                                                   STRAY left child's
                                                   diagnostic (true) with
                                                   "fork\n$ " (false)
     PSilent     "$ "                              a child died before
                                                   printing

   [PForkS] IS THE TERMINAL ROUND (lane PIPE-MODEL-3, design section
   4.3h, owner's ruling "strays" of 2026-09-21).  [runcmd]'s PIPE arm
   forks TWICE and does not wait between the forks: if [fork1] #2 fails
   after #1 succeeded, the runcmd child prints "fork\n" and exits while
   child 1 is ALIVE, and child 1's own [exec /echo] may fail -- so a
   STRAY writer prints a prefix of [dg_execL] at any later time,
   byte-interleaved with the panic, with sh's prompt and with anything
   after it.  The old constant [PFork] is the interleaving that got no
   stray byte, [PForkS (replicate (length alt_forkc) false)]
   ([pcont_forkS_old]).  What stops the interleaving from spreading into
   the NEXT round is discipline rule D4 ([d4_p]): a round whose block is
   a shuffle of the two sources is the LAST round of the covered
   session.

   [PPipe] AND [PForkS] END IN THE PROMPT, not in a fresh prologue: [runcmd]
   runs in the shell's forked child, so [panic] there exits the CHILD, the
   parent's [wait(0)] returns and it prints the next prompt.  The MAIN
   loop's own [fork1] panic -- which does kill the shell and re-enter
   init's prologue -- is [EchoDisc]'s alternative 3, i.e. [PEcho 3]. *)
Inductive palt :=
  | PEcho (a : nat)
  | PRan
  | PExecL
  | PExecR
  | PBoth (sel : list bool)
  | PPipe
  | PForkS (sel : list bool)
  | PSilent.

Global Instance palt_eq_dec : EqDecision palt.
Proof using. solve_decision. Defined.
Global Instance palt_inhabited : Inhabited palt := populate (PEcho 0%nat).

(* ---- THE INTERLEAVING AS A BINARY NUMERAL ---------------------------- *)

(* [sel] READ AS A BINARY NUMERAL WITH A LEADING 1, least significant bit
   first, so that leading [false]s survive the round trip: [bnum []] is the
   bare leading 1 and every entry doubles.  The leading 1 is what makes
   [bnum] injective -- without it [ [false] ] and [ [false; false] ] would
   both be 0.  Coordinator's ruling (2026-09-18): the code is POSITIONAL,
   not [encode_nat]'s pairing, so that a code is 34 bits at [|sel| = 33]
   instead of [encode_nat]'s ~66. *)
Fixpoint bnum (sel : list bool) : nat :=
  match sel with
  | [] => 1%nat
  | b :: s => ((if b then 1 else 0) + 2 * bnum s)%nat
  end.

Lemma bnum_pos sel : (0 < bnum sel)%nat.
Proof using. induction sel as [| [|] s IH]; cbn [bnum]; lia. Qed.

(* ...and the numeral is longer than the list, which is the fuel bound the
   decoder below runs on *)
Lemma bnum_gt_length sel : (length sel < bnum sel)%nat.
Proof using.
  induction sel as [| [|] s IH]; cbn [bnum length]; lia.
Qed.

(* THE DECODER, by structural recursion on a FUEL: strip bits off the
   bottom until only the leading 1 is left. *)
Fixpoint bdigits (f m : nat) : list bool :=
  match f with
  | 0%nat => []
  | S f' => if decide (m <= 1)%nat then []
            else bool_decide (Nat.modulo m 2 = 1%nat) :: bdigits f' (Nat.div m 2)
  end.

Definition bdec (m : nat) : list bool := bdigits m m.

(* the two readings of one binary digit *)
Lemma pd_mod2_add (d k : nat) : (d < 2)%nat -> Nat.modulo (d + 2 * k) 2 = d.
Proof using.
  intro Hd. replace (d + 2 * k)%nat with (d + k * 2)%nat by lia.
  rewrite Nat.Div0.mod_add Nat.mod_small; [reflexivity | exact Hd].
Qed.

Lemma pd_div2_add (d k : nat) : (d < 2)%nat -> Nat.div (d + 2 * k) 2 = k.
Proof using.
  intro Hd. replace (d + 2 * k)%nat with (k * 2 + d)%nat by lia.
  rewrite Nat.div_add_l; [| lia]. rewrite Nat.div_small; [lia | exact Hd].
Qed.

Lemma bdigits_bnum (f : nat) (sel : list bool) :
  (length sel < f)%nat -> bdigits f (bnum sel) = sel.
Proof using.
  revert sel. induction f as [| f IH]; intros sel Hf;
    [cbn [length] in Hf; lia |].
  destruct sel as [| b s].
  { cbn [bnum bdigits]. case_decide as H; [reflexivity | exfalso; lia]. }
  pose proof (bnum_pos s) as Hp.
  cbn [bnum bdigits length] in Hf |- *.
  case_decide as H1; [exfalso; destruct b; lia |].
  rewrite (pd_mod2_add (if b then 1%nat else 0%nat) (bnum s)
             ltac:(destruct b; lia))
          (pd_div2_add (if b then 1%nat else 0%nat) (bnum s)
             ltac:(destruct b; lia)).
  rewrite (IH s ltac:(lia)). f_equal.
  destruct b;
    [by rewrite bool_decide_eq_true_2 | by rewrite bool_decide_eq_false_2].
Qed.

Lemma bdec_bnum sel : bdec (bnum sel) = sel.
Proof using.
  rewrite /bdec. apply bdigits_bnum, bnum_gt_length.
Qed.

(* ...and the numeral is at least [2 ^ |sel|], which is the exact reason a
   [PBoth] code cannot be COMPUTED however cleverly it is laid out: [nat]
   is unary, and at the only [|sel|] the model admits ([palt_ok] forces
   [|dg_execL| + |dg_execR| = 33]) the code is a unary numeral with more
   than eight thousand million successors.  See [palt_code_both_big] and
   the note in section 8. *)
Lemma bnum_ge_pow2 sel : (2 ^ length sel <= bnum sel)%nat.
Proof using.
  induction sel as [| b s IH]; [cbn [length bnum Nat.pow]; lia |].
  cbn [length bnum]. rewrite Nat.pow_succ_r; [| lia]. destruct b; lia.
Qed.

(* ---- THE CODE ------------------------------------------------------- *)

(* THE ENCODING the stage's [cs_auth]/[cs_lb] machinery carries: an
   injective [nat] code, and the echo application's four are THEIR OWN
   INDEX, so an echo line's rounds are LITERALLY today's ([sessp_sess]).
   [PBoth sel] is encoded WITH [sel] -- one alternative per interleaving --
   so the transcript stays a function of [(ps, cs, I)].

   TEN SMALL CODES, THEN TWO ARITHMETIC PROGRESSIONS mod 16: codes 0..9 are
   the echo application's four and the six constant pipeline alternatives;
   above them tag 10 carries [PEcho] at an index the echo model never uses,
   and tag 11 carries [PBoth]'s numeral.  The decoder divides. *)
Definition palt_code (a : palt) : nat :=
  match a with
  | PEcho k => if decide (k < 4)%nat then k else (10 + 16 * (k - 4))%nat
  | PRan => 4%nat | PExecL => 5%nat | PExecR => 6%nat
  | PPipe => 7%nat | PSilent => 9%nat
  | PBoth sel => (11 + 16 * bnum sel)%nat
  | PForkS sel => (12 + 16 * bnum sel)%nat
  end.

Definition palt_of (n : nat) : palt :=
  if decide (n < 4)%nat then PEcho n
  else if decide (n = 4%nat) then PRan
  else if decide (n = 5%nat) then PExecL
  else if decide (n = 6%nat) then PExecR
  else if decide (n = 7%nat) then PPipe
  else if decide (n = 8%nat) then PSilent
  else if decide (n = 9%nat) then PSilent
  else if decide (Nat.modulo n 16 = 11%nat)
       then PBoth (bdec (Nat.div n 16))
       else if decide (Nat.modulo n 16 = 12%nat)
       then PForkS (bdec (Nat.div n 16))
       else PEcho (4 + Nat.div n 16)%nat.

Lemma pd_mod16_add (a m : nat) : Nat.modulo (a + 16 * m) 16 = Nat.modulo a 16.
Proof using.
  replace (a + 16 * m)%nat with (a + m * 16)%nat by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma pd_div16_add (a m : nat) :
  (a < 16)%nat -> Nat.div (a + 16 * m) 16 = m.
Proof using.
  intro Ha. replace (a + 16 * m)%nat with (m * 16 + a)%nat by lia.
  rewrite Nat.div_add_l; [| lia]. rewrite Nat.div_small; [lia | exact Ha].
Qed.

Lemma palt_of_code a : palt_of (palt_code a) = a.
Proof using.
  destruct a as [k | | | | sel | | sel |]; try (by vm_compute).
  - (* PEcho: its own index below 4, and out of every other code's way
       above it *)
    rewrite /palt_code. case_decide as Hk.
    + rewrite /palt_of decide_True; [reflexivity | exact Hk].
    + assert (Hm : Nat.modulo (10 + 16 * (k - 4)) 16 = 10%nat)
        by (rewrite pd_mod16_add; by vm_compute).
      rewrite /palt_of.
      do 7 (case_decide; [exfalso; lia |]).
      case_decide; [exfalso; congruence |].
      case_decide; [exfalso; congruence |].
      rewrite (pd_div16_add 10 (k - 4)%nat ltac:(lia)). f_equal. lia.
  - (* PBoth: the interleaving through its binary numeral *)
    pose proof (bnum_pos sel) as Hp.
    assert (Hm : Nat.modulo (11 + 16 * bnum sel) 16 = 11%nat)
      by (rewrite pd_mod16_add; by vm_compute).
    rewrite /palt_code /palt_of.
    do 7 (case_decide; [exfalso; lia |]).
    case_decide; [| exfalso; congruence].
    rewrite (pd_div16_add 11 (bnum sel) ltac:(lia)).
    by rewrite bdec_bnum.
  - (* PForkS: the terminal round's interleaving, at the next tag *)
    pose proof (bnum_pos sel) as Hp.
    assert (Hm : Nat.modulo (12 + 16 * bnum sel) 16 = 12%nat)
      by (rewrite pd_mod16_add; by vm_compute).
    rewrite /palt_code /palt_of.
    do 7 (case_decide; [exfalso; lia |]).
    case_decide; [exfalso; congruence |].
    case_decide; [| exfalso; congruence].
    rewrite (pd_div16_add 12 (bnum sel) ltac:(lia)).
    by rewrite bdec_bnum.
Qed.

(* ...hence the code is INJECTIVE, which is all the stage asks of it *)
Lemma palt_code_inj (a b : palt) : palt_code a = palt_code b -> a = b.
Proof using.
  intro H. by rewrite -(palt_of_code a) -(palt_of_code b) H.
Qed.

Lemma palt_of_lt4 n : (n < 4)%nat -> palt_of n = PEcho n.
Proof using. intro H. rewrite /palt_of decide_True; [reflexivity | exact H]. Qed.

Lemma palt_code_echo_lt4 k : (k < 4)%nat -> palt_code (PEcho k) = k.
Proof using.
  intro H. rewrite /palt_code decide_True; [reflexivity | exact H].
Qed.

(* THE PROLOGUE-RE-ENTERING ALTERNATIVE: the MAIN loop's [fork1] panicked,
   init reaped the SHELL and its outer loop opened a NEW prologue round.
   [PPipe] and [PForkS] are NOT of this kind -- they panic in the runcmd
   child and the shell lives. *)
Definition palt_panic (a : palt) : bool :=
  match a with PEcho k => bool_decide (k = 3%nat) | _ => false end.

(* WHICH ALTERNATIVES A LINE SHAPE ADMITS, and [sel]'s shape: an
   interleaving names one byte per byte of the two diagnostics, and
   [count_true] many of them come from the left one. *)
Definition palt_ok (l : pline) (a : palt) : Prop :=
  match l with
  | LEcho _ => match a with PEcho k => (k < 4)%nat | _ => False end
  | LPipe _ =>
      match a with
      | PBoth sel =>
          length sel = (length dg_execL + length dg_execR)%nat
          /\ count_true sel = length dg_execL
      | PForkS sel =>
          sel <> []
          /\ (count_true sel <= length dg_execL)%nat
          /\ (length sel - count_true sel <= length alt_forkc)%nat
      | PRan | PExecL | PExecR | PPipe | PSilent => True
      | PEcho k => k = 3%nat
      end
  end.

Global Instance palt_ok_dec l a : Decision (palt_ok l a).
Proof using. destruct l, a; rewrite /palt_ok; apply _. Defined.

(* ---- DESIGN SECTION 1'S HOLE, AS RULED ------------------------------- *)

(* THE MAIN LOOP'S OWN [fork1] PANIC IS AVAILABLE AT A PIPELINE LINE TOO.
   Design section 1's table said [PEcho] was "LEcho lines only" while its
   prose said the echo application's [alt_panic] arm -- sh's MAIN-loop
   [fork1] failing, which kills the SHELL and re-enters init's prologue --
   "is unchanged and [LPipe] lines reach it exactly as [LEcho] lines do (it
   is decided before the line is parsed)".  The lane reported the
   contradiction (the machine CAN put [alt_panic] and then a FRESH
   PROLOGUE on the wire in a pipeline round, and no other [LPipe]
   alternative prints that: [PForkS] prints a shuffle of [alt_panic ++
   u_prompt] with the stray's diagnostic, which
   parts from it at byte 5 whenever the re-entered prologue carries the
   banner -- so the theorem at the old table would have been FALSE, not
   vacuous), and the coordinator RULED for the prose (2026-09-18): exactly
   [PEcho 3] joins the pipeline line's alternatives.  [pcont (LPipe ws)
   (PEcho 3) = alt_panic] already, and [palt_panic] already fires, so
   [alt_cont_p] appends the re-entered prologue at a pipeline line exactly
   as at an echo line, with no other change to the session. *)
Lemma palt_ok_pipe_echo (ws : list (list (bv 8))) (k : nat) :
  palt_ok (LPipe ws) (PEcho k) <-> k = 3%nat.
Proof using. done. Qed.

Lemma palt_ok_pipe_panic (ws : list (list (bv 8))) :
  palt_ok (LPipe ws) (PEcho 3%nat).
Proof using. reflexivity. Qed.

(* THE ARITHMETIC OBSTACLE, PROVED RATHER THAN TIMED.  Every interleaving
   the model admits has [|sel| = 33], so its code exceeds [2 ^ 33].  That
   is a unary [nat] of more than 8.5 thousand million successors: no
   [vm_compute], and no other layout of the code, can build it -- an
   injective map out of the admitted interleavings alone already needs
   values past [C(33,17) > 10 ^ 9].  The model is unaffected, because
   nothing in the theorem computes a code and [palt_of_code] is proved
   abstractly; what is affected is every WITNESS, which is why the two
   [PBoth] demos of section 8 rewrite with [palt_of_code] instead. *)
Lemma palt_code_both_big (ws : list (list (bv 8))) (sel : list bool) :
  palt_ok (LPipe ws) (PBoth sel) -> (2 ^ 33 <= palt_code (PBoth sel))%nat.
Proof using.
  intros [Hlen _].
  pose proof (bnum_ge_pow2 sel) as Hp. rewrite Hlen in Hp.
  rewrite dg_execL_len dg_execR_len in Hp.
  replace (17 + 16)%nat with 33%nat in Hp by lia.
  rewrite /palt_code. lia.
Qed.

(* the panic alternative is the SAME one at both line shapes, so the
   determinacy proof never has to know which shape it is looking at *)
Lemma palt_panic_3 (l : pline) (a : palt) :
  palt_ok l a -> palt_panic a = true -> a = PEcho 3%nat.
Proof using.
  destruct a as [k | | | | sel | | sel |]; intros Ha Hp; try discriminate.
  rewrite /palt_panic in Hp. apply bool_decide_eq_true in Hp as ->.
  reflexivity.
Qed.

Lemma palt_ok_echo_lt4 ws c : palt_ok (LEcho ws) (palt_of c) -> (c < 4)%nat.
Proof using.
  rewrite /palt_of. case_decide as H4; [by intros _ |].
  do 6 (case_decide; [by intros [] |]).
  case_decide; [by intros [] |].
  case_decide; [by intros [] | rewrite /palt_ok; lia].
Qed.

(* ---- THE TERMINAL ROUND'S ALTERNATIVE, AND THE OLD [PFork] ---------- *)

(* the one-bit reading every consumer takes: IS this round the terminal
   fork-failure one? *)
Definition palt_isforkS (a : palt) : bool :=
  match a with PForkS _ => true | _ => false end.

Lemma palt_isforkS_code (sel : list bool) :
  palt_isforkS (palt_of (palt_code (PForkS sel))) = true.
Proof using. by rewrite palt_of_code. Qed.

Lemma palt_isforkS_inv (a : palt) :
  palt_isforkS a = true -> exists sel, a = PForkS sel.
Proof using. destruct a; try discriminate. intros _. by eexists. Qed.

(* only a PIPELINE line admits the terminal fork-failure alternative *)
Lemma palt_ok_forkS_pipe (l : pline) (sel : list bool) :
  palt_ok l (PForkS sel) -> pline_is_pipe l = true.
Proof using. destruct l; [by intros [] | reflexivity]. Qed.

Lemma palt_ok_isforkS_pipe (l : pline) (a : palt) :
  palt_ok l a -> palt_isforkS a = true -> pline_is_pipe l = true.
Proof using.
  intros Ha Hf. destruct (palt_isforkS_inv a Hf) as [sel ->].
  exact (palt_ok_forkS_pipe l sel Ha).
Qed.

Lemma palt_panic_forkS (sel : list bool) : palt_panic (PForkS sel) = false.
Proof using. reflexivity. Qed.

(* THE OLD [PFork] IS [PForkS] AT THE SELECTOR THAT TOOK NO STRAY BYTE.
   Design section 4.3h says "[PForkS []] is the old [PFork]"; it is NOT
   ([pcont] at the empty selector is the EMPTY block, and [palt_ok]
   refuses it).  [false] is the RIGHT source ([alt_forkc]) because the
   stage's [PipeBothPure.pend2 R sel] is [pmerge sel dg_execL R] and the
   runcmd child holds the RIGHT cursor (design section 4.3h's own stage
   paragraph: "the right source gains a third mode [alt_forkc]"), so the
   design's [pmerge sel alt_forkc (... dg_execL)] has its two sources
   the wrong way round. *)
Definition sel_forkc : list bool := replicate (length alt_forkc) false.

Lemma palt_ok_forkS_old (ws : list (list (bv 8))) :
  palt_ok (LPipe ws) (PForkS sel_forkc).
Proof using.
  rewrite /palt_ok /sel_forkc. split.
  { intro Hq. apply (f_equal length) in Hq.
    rewrite length_replicate alt_forkc_len in Hq. cbn [length] in Hq. lia. }
  rewrite count_true_replicate_false length_replicate. lia.
Qed.


Lemma palt_panic_echo c :
  (c < 4)%nat -> palt_panic (palt_of c) = bool_decide (c = 3%nat).
Proof using. intro H. by rewrite (palt_of_lt4 c H). Qed.

(* ---- THE CONSOLE CONTINUATION OF A ROUND ----------------------------- *)

(* At [PEcho] it is [EchoDisc.line_alts_of] verbatim; at [PRan] it is
   [EchoDisc.line_alts_of]'s GOOD alternative, because cat copies. *)
Definition pcont (l : pline) (a : palt) : list (bv 8) :=
  match a with
  | PEcho k => line_alts_of (pline_ws l) !!! k
  | PRan => wl_line (drop 1 (pline_ws l)) ++ u_prompt
  | PExecL => alt_execL
  | PExecR => alt_execR
  | PBoth sel => pmerge sel dg_execL dg_execR ++ u_prompt
  | PPipe => alt_pipe
  | PForkS sel => pmerge sel dg_execL alt_forkc
  | PSilent => u_prompt
  end.

(* THE CHEAPNESS OF THE CLAIM, in one equation: a pipeline round that ran
   prints exactly what the echo line prints. *)
Lemma pcont_PRan_alt0 l : pcont l PRan = line_alts_of (pline_ws l) !!! 0%nat.
Proof using. reflexivity. Qed.

Lemma pcont_forkS_old (ws : list (list (bv 8))) :
  pcont (LPipe ws) (PForkS sel_forkc) = alt_forkc.
Proof using.
  rewrite /pcont /sel_forkc.
  rewrite (pmerge_all_false_gen (length alt_forkc) dg_execL alt_forkc).
  by rewrite take_ge.
Qed.

(* EVERY ADMITTED TERMINAL BLOCK PASSES THE SHUFFLE TEST -- the
   completeness half of [pmergeable], and the reason [pcont_pair_det]'s
   new premise is discharged by discipline rule D4 and by nothing else. *)
Lemma pmergeable_forkS (l : pline) (sel : list bool) :
  palt_ok l (PForkS sel) -> pmergeable (pcont l (PForkS sel)).
Proof using.
  destruct l as [ws | ws]; [by intros [] |]. intros (_ & H1 & H2).
  rewrite /pmergeable /pcont. by apply shufb_pmerge.
Qed.

Lemma pmergeable_isforkS (l : pline) (a : palt) :
  palt_ok l a -> palt_isforkS a = true -> pmergeable (pcont l a).
Proof using.
  intros Ha Hf. destruct (palt_isforkS_inv a Hf) as [sel ->].
  exact (pmergeable_forkS l sel Ha).
Qed.

Lemma pcont_panic l a : palt_panic a = true -> pcont l a = alt_panic.
Proof using.
  destruct a; try discriminate.
  rewrite /palt_panic. intro Hk. apply bool_decide_eq_true in Hk as ->.
  exact (line_alts_of_3 (pline_ws l)).
Qed.

(* THE ENGINE OF THE DETERMINACY ARGUMENT: a non-panic alternative prints
   a '$'-free run and then sh's prompt.  There is no third shape, at
   either line.  (Design section 1 asked whether EVERY continuation
   satisfies the shape: every one but [PEcho 3] does -- [PPipe] and
   [PForkS] ends in the prompt too -- and [PEcho 3] is the one the prologue
   follows.) *)
(* AN ADMITTED INTERLEAVING IS NONEMPTY AND OPENS ON 'e'.  Both exec
   diagnostics start with "exec", so whichever child got the wire first,
   the round's first byte is 'e' -- and sh's panic line opens on 'f',
   which is what settles the [PBoth]-against-panic comparison below. *)
Lemma pcont_both_head_e (l : pline) (sel : list bool) :
  palt_ok l (PBoth sel) ->
  pmerge sel dg_execL dg_execR !! 0%nat = Some (Z_to_bv 8 101%Z).
Proof using.
  destruct l as [ws | ws]; [by intros [] |]. intros [Hlen Hcnt].
  assert (HeL : dg_execL !! 0%nat = Some (Z_to_bv 8 101%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HeR : dg_execR !! 0%nat = Some (Z_to_bv 8 101%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hml : length (pmerge sel dg_execL dg_execR) = length sel)
    by (apply pmerge_length; lia).
  destruct (pmerge sel dg_execL dg_execR) as [| x r] eqn:Hm.
  { exfalso. rewrite Hlen dg_execL_len dg_execR_len in Hml.
    cbn [length] in Hml. lia. }
  assert (Hx : pmerge sel dg_execL dg_execR !! 0%nat = Some x)
    by (rewrite Hm; reflexivity).
  destruct (pmerge_head sel dg_execL dg_execR x Hx) as [H | H];
    [rewrite HeL in H | rewrite HeR in H];
    injection H as Hxe; rewrite -Hxe; reflexivity.
Qed.

Lemma pcont_shape (l : pline) (a : palt) :
  pline_ok l -> palt_ok l a -> palt_panic a = false ->
  palt_isforkS a = false ->
  exists u, pcont l a = u ++ u_prompt /\ Forall nodollar u.
Proof using.
  intros Hl Ha Hp Hf.
  assert (Hex : wl_wf dg_exec)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hec : wl_wf dg_exec_cat)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hpi : wl_wf dg_pipe)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hfk : wl_wf dg_fork)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hpr : exists u : list (bv 8), u_prompt = u ++ u_prompt
                  /\ Forall nodollar u).
  { exists []. split; [reflexivity | constructor]. }
  destruct a; rewrite /pcont; [| | | | | | discriminate |].
  - (* PEcho: the echo application's four, minus the panic one.  At a
       PIPELINE line the only [PEcho] admitted IS the panic one, so the
       hypothesis refutes the case outright. *)
    rewrite /palt_panic in Hp. apply bool_decide_eq_false in Hp.
    rewrite /palt_ok in Ha. destruct l as [ws | ws]; [| by destruct (Hp Ha)].
    destruct a as [| [| [| [| a]]]]; [| | | done | exfalso; lia].
    + exists (wl_line (drop 1 ws)). rewrite line_alts_of_0.
      split; [reflexivity |].
      apply (pd_wl_line_shape (drop 1 ws)).
      apply lb_Forall_drop, (line_ok_wf _ Hl).
    + exists (wl_line dg_exec). rewrite line_alts_of_1 /alt_execfail.
      split; [reflexivity |]. apply (pd_wl_line_shape dg_exec Hex).
    + rewrite line_alts_of_2 /alt_prompt. exact Hpr.
  - (* PRan: the line, minus the command name, then the prompt *)
    exists (wl_line (drop 1 (pline_ws l))). split; [reflexivity |].
    apply (pd_wl_line_shape (drop 1 (pline_ws l))).
    apply lb_Forall_drop, (line_ok_wf _ (pline_ok_ws l Hl)).
  - exists dg_execL. rewrite /alt_execL. split; [reflexivity |].
    rewrite /dg_execL. apply (pd_wl_line_shape dg_exec Hex).
  - exists dg_execR. rewrite /alt_execR. split; [reflexivity |].
    rewrite /dg_execR. apply (pd_wl_line_shape dg_exec_cat Hec).
  - exists (pmerge sel dg_execL dg_execR). split; [reflexivity |].
    exact (pmerge_no_dollar sel).
  - exists (wl_line dg_pipe). rewrite /alt_pipe. split; [reflexivity |].
    apply (pd_wl_line_shape dg_pipe Hpi).
  - exact Hpr.
Qed.

(* ...AND THE STRONGER SHAPE THE PANIC COMPARISON NEEDS: the run's only
   newline, if any, is its LAST byte -- OR the run opens on 'e', which sh's
   panic line, opening on 'f', can never match.  [FileDisc.cont_shape]
   gives the newline half at every alternative; HERE IT IS FALSE at
   [PBoth] ([pcont_both_no_nl_shape] below), because a merge of the two
   diagnostics carries TWO newlines.  The second arm is what replaces it,
   and it is all [pcont_pair_det] wants: the only comparison that spends
   this lemma puts sh's panic line on the other side. *)
Lemma pcont_shape_nl (l : pline) (a : palt) :
  pline_ok l -> palt_ok l a -> palt_panic a = false ->
  palt_isforkS a = false ->
  exists u, pcont l a = u ++ u_prompt
            /\ Forall nodollar u
            /\ ((wl_nl ∉ u \/ exists v, wl_nl ∉ v /\ u = v ++ [wl_nl])
                \/ u !! 0%nat = Some (Z_to_bv 8 101%Z)).
Proof using.
  intros Hl Ha Hp Hf.
  assert (Hex : wl_wf dg_exec)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hec : wl_wf dg_exec_cat)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hpi : wl_wf dg_pipe)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hfk : wl_wf dg_fork)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hpr : exists u : list (bv 8), u_prompt = u ++ u_prompt
                  /\ Forall nodollar u
                  /\ ((wl_nl ∉ u \/ exists v, wl_nl ∉ v /\ u = v ++ [wl_nl])
                      \/ u !! 0%nat = Some (Z_to_bv 8 101%Z))).
  { exists []. split; [reflexivity |]. split; [constructor |].
    left. left. apply not_elem_of_nil. }
  destruct a as [k | | | | sel | | sel |]; rewrite /pcont;
    [| | | | | | discriminate |].
  - (* PEcho: at a PIPELINE line the only one admitted panics *)
    rewrite /palt_panic in Hp. apply bool_decide_eq_false in Hp.
    rewrite /palt_ok in Ha. destruct l as [ws | ws]; [| by destruct (Hp Ha)].
    destruct k as [| [| [| [| k]]]]; [| | | done | exfalso; lia].
    + exists (wl_line (drop 1 ws)). rewrite line_alts_of_0.
      split; [reflexivity |].
      destruct (pd_wl_line_shape' (drop 1 ws)
                  ltac:(apply lb_Forall_drop, (line_ok_wf _ Hl)))
        as [H1 H2].
      split; [exact H1 | by left].
    + exists (wl_line dg_exec). rewrite line_alts_of_1 /alt_execfail.
      split; [reflexivity |].
      destruct (pd_wl_line_shape' dg_exec Hex) as [H1 H2].
      split; [exact H1 | by left].
    + rewrite line_alts_of_2 /alt_prompt. exact Hpr.
  - (* PRan *)
    exists (wl_line (drop 1 (pline_ws l))). split; [reflexivity |].
    destruct (pd_wl_line_shape' (drop 1 (pline_ws l))
                ltac:(apply lb_Forall_drop,
                      (line_ok_wf _ (pline_ok_ws l Hl)))) as [H1 H2].
    split; [exact H1 | by left].
  - exists dg_execL. rewrite /alt_execL. split; [reflexivity |].
    destruct (pd_wl_line_shape' dg_exec Hex) as [H1 H2].
    split; [exact H1 | by left].
  - exists dg_execR. rewrite /alt_execR. split; [reflexivity |].
    destruct (pd_wl_line_shape' dg_exec_cat Hec) as [H1 H2].
    split; [exact H1 | by left].
  - (* PBoth: the newline half is FALSE here; the head byte is 'e' *)
    exists (pmerge sel dg_execL dg_execR). split; [reflexivity |].
    split; [exact (pmerge_no_dollar sel) |]. right.
    exact (pcont_both_head_e l sel Ha).
  - exists (wl_line dg_pipe). rewrite /alt_pipe. split; [reflexivity |].
    destruct (pd_wl_line_shape' dg_pipe Hpi) as [H1 H2].
    split; [exact H1 | by left].
  - exact Hpr.
Qed.

(* ---- WHY THE STRONGER SHAPE IS FALSE AT [PBoth] ---------------------- *)

(* the interleaving that prints the left diagnostic and then the right one *)
Definition sel_LR : list bool :=
  replicate (length dg_execL) true ++ replicate (length dg_execR) false.

Lemma sel_LR_ok ws : palt_ok (LPipe ws) (PBoth sel_LR).
Proof using.
  rewrite /palt_ok /sel_LR. split.
  - rewrite length_app !length_replicate. reflexivity.
  - rewrite count_true_app count_true_replicate_true
            count_true_replicate_false. lia.
Qed.

Lemma pmerge_sel_LR : pmerge sel_LR dg_execL dg_execR = dg_execL ++ dg_execR.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* TWO NEWLINES, so the run is neither newline-free nor closed by its one
   newline: [FileDisc.cont_shape]'s disjunct is refuted at this [sel]. *)
Lemma pcont_both_no_nl_shape :
  ~ (wl_nl ∉ (dg_execL ++ dg_execR)
     \/ exists v, wl_nl ∉ v /\ dg_execL ++ dg_execR = v ++ [wl_nl]).
Proof using.
  assert (Hin : wl_nl ∈ dg_execL ++ dg_execR)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hat : (dg_execL ++ dg_execR) !! 16%nat = Some wl_nl)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hlen : length (dg_execL ++ dg_execR) = 33%nat)
    by (by vm_compute).
  intros [Hno | (v & Hv & Heq)]; [by destruct (Hno Hin) |].
  assert (Hvl : length v = 32%nat)
    by (apply (f_equal length) in Heq;
        rewrite Hlen length_app in Heq; cbn [length] in Heq; lia).
  rewrite Heq in Hat.
  rewrite (lookup_app_l v [wl_nl] 16%nat ltac:(lia)) in Hat.
  exact (Hv (elem_of_list_lookup_2 v 16%nat wl_nl Hat)).
Qed.

(* ====================================================================== *)
(*  4.  THE SESSION                                                        *)
(*                                                                        *)
(*  [EchoDisc.sess] with the richer alternative, read through the          *)
(*  encoding.  NOTHING IS THREADED: a pipe dies with its era (design       *)
(*  section 0, limit 3), so unlike [FileDisc.sessf] there is no state      *)
(*  parameter and the laws are [EchoDisc.sess]'s at the letter.            *)
(* ====================================================================== *)

(* the alternative round [i] took, decoded; out of range it reads the
   inhabitant, which keeps every function below TOTAL exactly as
   [EchoDisc]'s do -- the choices are pinned by the wire wherever the
   discipline actually looks at them *)
Definition palt_at (cs : list nat) (i : nat) : palt := palt_of (cs !!! i).

(* how many shells have died on their own MAIN-loop fork panic BEFORE line
   [i] -- [EchoDisc.pro_idx] at [palt_panic] *)
Fixpoint pro_idx_p (cs : list nat) (i : nat) : nat :=
  match i with
  | 0%nat => 0%nat
  | S i' => (pro_idx_p cs i' + if palt_panic (palt_at cs i') then 1 else 0)%nat
  end.

Definition alt_cont_p (ps cs : list nat) (bs : list (list (bv 8))) (i : nat)
  : list (bv 8) :=
  pcont (pline_of (bs !!! i)) (palt_at cs i)
  ++ (if palt_panic (palt_at cs i)
      then pro_of (pro_from (S (pro_idx_p cs i)) ps) else []).

Definition alt_blk_p (ps cs : list nat) (bs : list (list (bv 8))) (i : nat)
  : list (bv 8) :=
  bs !!! i ++ wl_nl :: alt_cont_p ps cs bs i.

Definition alt_seq_p (ps cs : list nat) (bs : list (list (bv 8))) (q : nat)
  : list (bv 8) :=
  concat (alt_blk_p ps cs bs <$> List.seq 0 q).

(* THE EXPECTED SESSION TRANSCRIPT for the era's input [I]: the prologue
   this run opened with, then one block per COMPLETED line, then the echo
   of the line in progress. *)
Definition sessp (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  pro_of ps ++ alt_seq_p ps cs (bodies_of I) (nlines I) ++ rest_of I.

(* ---- the round pointer ----------------------------------------------- *)

Lemma pro_idx_p_S cs i :
  pro_idx_p cs (S i)
  = (pro_idx_p cs i + if palt_panic (palt_at cs i) then 1 else 0)%nat.
Proof using. reflexivity. Qed.

Lemma pro_idx_p_Sp cs i :
  palt_panic (palt_at cs i) = true -> pro_idx_p cs (S i) = S (pro_idx_p cs i).
Proof using. intro H. rewrite pro_idx_p_S H. lia. Qed.

Lemma pro_idx_p_Sn cs i :
  palt_panic (palt_at cs i) = false -> pro_idx_p cs (S i) = pro_idx_p cs i.
Proof using. intro H. rewrite pro_idx_p_S H. lia. Qed.

Lemma pro_idx_p_mono cs i j :
  (i <= j)%nat -> (pro_idx_p cs i <= pro_idx_p cs j)%nat.
Proof using.
  intros Hij. induction j as [| j IH].
  - assert (i = 0%nat) by lia. by subst i.
  - destruct (decide (i = S j)) as [-> | Hne]; [done |].
    rewrite pro_idx_p_S.
    assert (pro_idx_p cs i <= pro_idx_p cs j)%nat by (apply IH; lia).
    destruct (palt_panic (palt_at cs j)); lia.
Qed.

Lemma pro_idx_p_le cs i : (pro_idx_p cs i <= i)%nat.
Proof using.
  induction i as [| i IH]; [cbn; lia |].
  rewrite pro_idx_p_S. destruct (palt_panic (palt_at cs i)); lia.
Qed.

Lemma pro_idx_p_S_le cs i : (pro_idx_p cs (S i) <= S (pro_idx_p cs i))%nat.
Proof using.
  rewrite pro_idx_p_S. destruct (palt_panic (palt_at cs i)); lia.
Qed.

Lemma pro_idx_p_ext cs1 cs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  forall j, (j <= q)%nat -> pro_idx_p cs1 j = pro_idx_p cs2 j.
Proof using.
  intros Hj j. induction j as [| j IH]; intros Hjq; [done |].
  rewrite !pro_idx_p_S IH; [| lia].
  by rewrite /palt_at (Hj j ltac:(lia)).
Qed.

Lemma pro_idx_p_take cs q i :
  (i <= q)%nat -> pro_idx_p (take q cs) i = pro_idx_p cs i.
Proof using.
  intros Hi. apply (pro_idx_p_ext _ _ q); [| lia].
  intros j Hj. rewrite list_lookup_total_alt lookup_take; [| lia].
  by rewrite -list_lookup_total_alt.
Qed.

Lemma pro_idx_p_add cs n i :
  pro_idx_p cs (n + i) = (pro_idx_p cs n + pro_idx_p (drop n cs) i)%nat.
Proof using.
  induction i as [| i IH]; [rewrite Nat.add_0_r; cbn [pro_idx_p]; lia |].
  rewrite Nat.add_succ_r !pro_idx_p_S IH /palt_at lb_lookup_total_drop.
  destruct (palt_panic (palt_of (cs !!! (n + i)))); lia.
Qed.

(* ---- the block sequence ---------------------------------------------- *)

Lemma alt_seq_p_0 ps cs bs : alt_seq_p ps cs bs 0 = [].
Proof using. reflexivity. Qed.

Lemma alt_seq_p_S ps cs bs q :
  alt_seq_p ps cs bs (S q) = alt_seq_p ps cs bs q ++ alt_blk_p ps cs bs q.
Proof using.
  rewrite /alt_seq_p List.seq_S fmap_app concat_app Nat.add_0_l /=.
  by rewrite app_nil_r.
Qed.

Lemma alt_cont_p_bs ps cs bs bs' i :
  bs !!! i = bs' !!! i -> alt_cont_p ps cs bs i = alt_cont_p ps cs bs' i.
Proof using. intro H. by rewrite /alt_cont_p H. Qed.

Lemma alt_blk_p_bs ps cs bs bs' i :
  bs !!! i = bs' !!! i -> alt_blk_p ps cs bs i = alt_blk_p ps cs bs' i.
Proof using.
  intro H. by rewrite /alt_blk_p H (alt_cont_p_bs ps cs bs bs' i H).
Qed.

Lemma alt_blk_p_length ps cs bs q :
  length (alt_blk_p ps cs bs q)
  = (length (bs !!! q) + 1 + length (alt_cont_p ps cs bs q))%nat.
Proof using.
  rewrite /alt_blk_p (length_app (bs !!! q) (wl_nl :: alt_cont_p ps cs bs q)).
  cbn [length]. lia.
Qed.

Lemma alt_seq_p_S_length ps cs bs q :
  length (alt_seq_p ps cs bs (S q))
  = (length (alt_seq_p ps cs bs q) + length (bs !!! q) + 1
     + length (alt_cont_p ps cs bs q))%nat.
Proof using.
  rewrite alt_seq_p_S (length_app (alt_seq_p ps cs bs q) _) alt_blk_p_length.
  lia.
Qed.

Lemma alt_blk_p_ext ps1 ps2 cs1 cs2 bs1 bs2 q :
  (forall j, (j <= q)%nat -> cs1 !!! j = cs2 !!! j) ->
  (forall j, (j <= q)%nat -> bs1 !!! j = bs2 !!! j) ->
  (forall r, (r <= pro_idx_p cs1 (S q))%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_blk_p ps1 cs1 bs1 q = alt_blk_p ps2 cs2 bs2 q.
Proof using.
  intros Hc Hb Hr. rewrite /alt_blk_p /alt_cont_p.
  rewrite (Hb q ltac:(lia)) /palt_at (Hc q ltac:(lia)).
  destruct (palt_panic (palt_of (cs2 !!! q))) eqn:Hpa; [| reflexivity].
  rewrite (pro_idx_p_ext cs1 cs2 q ltac:(intros j Hj; apply Hc; lia) q
             ltac:(lia)).
  rewrite (Hr (S (pro_idx_p cs2 q))); [reflexivity |].
  rewrite pro_idx_p_S -(pro_idx_p_ext cs1 cs2 q
            ltac:(intros j Hj; apply Hc; lia) q ltac:(lia)).
  rewrite /palt_at -(Hc q ltac:(lia)) in Hpa. rewrite Hpa. lia.
Qed.

Lemma alt_seq_p_ext ps1 ps2 cs1 cs2 bs1 bs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  (forall j, (j < q)%nat -> bs1 !!! j = bs2 !!! j) ->
  (forall r, (r <= pro_idx_p cs1 q)%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_seq_p ps1 cs1 bs1 q = alt_seq_p ps2 cs2 bs2 q.
Proof using.
  induction q as [| q IH]; intros Hc Hb Hr; [reflexivity |].
  rewrite !alt_seq_p_S.
  rewrite (IH ltac:(intros j Hj; apply Hc; lia)
              ltac:(intros j Hj; apply Hb; lia)
              ltac:(intros r Hr'; apply Hr;
                    pose proof (pro_idx_p_mono cs1 q (S q) ltac:(lia)); lia)).
  by rewrite (alt_blk_p_ext ps1 ps2 cs1 cs2 bs1 bs2 q
                ltac:(intros j Hj; apply Hc; lia)
                ltac:(intros j Hj; apply Hb; lia) Hr).
Qed.

Lemma alt_seq_p_bs_ext ps cs bs1 bs2 q :
  (forall j, (j < q)%nat -> bs1 !!! j = bs2 !!! j) ->
  alt_seq_p ps cs bs1 q = alt_seq_p ps cs bs2 q.
Proof using. intro Hb. by apply (alt_seq_p_ext ps ps cs cs bs1 bs2 q). Qed.

Lemma alt_seq_p_bs_app ps cs bs bs' q :
  (q <= length bs)%nat -> alt_seq_p ps cs (bs ++ bs') q = alt_seq_p ps cs bs q.
Proof using.
  intro Hq. apply alt_seq_p_bs_ext. intros j Hj.
  rewrite !list_lookup_total_alt lookup_app_l; [reflexivity | lia].
Qed.

Lemma alt_seq_p_cs_ext ps cs1 cs2 bs q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  alt_seq_p ps cs1 bs q = alt_seq_p ps cs2 bs q.
Proof using. intro Hc. by apply (alt_seq_p_ext ps ps cs1 cs2 bs bs q). Qed.

Lemma alt_seq_p_ps_ext ps1 ps2 cs bs q :
  (forall r, (r <= pro_idx_p cs q)%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_seq_p ps1 cs bs q = alt_seq_p ps2 cs bs q.
Proof using. intro Hr. by apply (alt_seq_p_ext ps1 ps2 cs cs bs bs q). Qed.

(* ---- dropping the first block, which is what the induction consumes -- *)

Lemma alt_cont_p_drop ps cs bs n i :
  alt_cont_p (pro_from (pro_idx_p cs n) ps) (drop n cs) (drop n bs) i
  = alt_cont_p ps cs bs (n + i).
Proof using.
  rewrite /alt_cont_p !lb_lookup_total_drop /palt_at !lb_lookup_total_drop.
  f_equal.
  destruct (palt_panic (palt_of (cs !!! (n + i)))); [| reflexivity].
  rewrite pro_from_add pro_idx_p_add. f_equal. f_equal. lia.
Qed.

Lemma alt_blk_p_drop ps cs bs n i :
  alt_blk_p (pro_from (pro_idx_p cs n) ps) (drop n cs) (drop n bs) i
  = alt_blk_p ps cs bs (n + i).
Proof using.
  by rewrite /alt_blk_p lb_lookup_total_drop alt_cont_p_drop.
Qed.

Lemma alt_seq_p_cons ps cs bs q :
  alt_seq_p ps cs bs (S q)
  = alt_blk_p ps cs bs 0%nat
    ++ alt_seq_p (pro_from (pro_idx_p cs 1%nat) ps) (drop 1 cs) (drop 1 bs) q.
Proof using.
  rewrite /alt_seq_p.
  replace (List.seq 0 (S q)) with (0%nat :: List.seq 1 q) by reflexivity.
  rewrite fmap_cons concat_cons. f_equal.
  rewrite -List.seq_shift -list_fmap_compose.
  f_equal. apply list_fmap_ext.
  intros i x Hx. rewrite /compose. by rewrite (alt_blk_p_drop ps cs bs 1 x).
Qed.

Lemma alt_seq_p_cons_assoc ps cs bs q (t : list (bv 8)) :
  alt_seq_p ps cs bs (S q) ++ t
  = bs !!! 0%nat
    ++ wl_nl :: (alt_cont_p ps cs bs 0%nat
                 ++ (alt_seq_p (pro_from (pro_idx_p cs 1%nat) ps) (drop 1 cs)
                       (drop 1 bs) q ++ t)).
Proof using. rewrite alt_seq_p_cons /alt_blk_p. apply lb_app4. Qed.

(* ---- THE SESSION'S LAWS, at [EchoDisc.sess]'s statements ------------- *)

Lemma sessp_nil ps cs : sessp ps cs [] = pro_of ps.
Proof using.
  rewrite /sessp rest_of_nil nlines_nil alt_seq_p_0. by rewrite !app_nil_r.
Qed.

Lemma sessp_length ps cs I :
  length (sessp ps cs I)
  = (length (pro_of ps) + length (alt_seq_p ps cs (bodies_of I) (nlines I))
     + length (rest_of I))%nat.
Proof using.
  rewrite /sessp (length_app (pro_of ps) _)
    (length_app (alt_seq_p ps cs (bodies_of I) (nlines I)) (rest_of I)). lia.
Qed.

Lemma sessp_snoc_other ps cs I b :
  b <> wl_nl -> sessp ps cs (I ++ [b]) = sessp ps cs I ++ [b].
Proof using.
  intro Hb. rewrite /sessp (bodies_of_snoc_other I b Hb)
    (nlines_snoc_other I b Hb) (rest_of_snoc_other I b Hb).
  by rewrite !app_assoc.
Qed.

Lemma sessp_snoc_nl ps cs I :
  sessp ps cs (I ++ [wl_nl])
  = sessp ps cs I
    ++ wl_nl :: alt_cont_p ps cs (bodies_of I ++ [rest_of I]) (nlines I).
Proof using.
  assert (Hidx : (bodies_of I ++ [rest_of I]) !!! (nlines I) = rest_of I).
  { rewrite list_lookup_total_alt
      (lookup_app_r (bodies_of I) [rest_of I] (nlines I)
         ltac:(rewrite /nlines; lia)).
    rewrite /nlines Nat.sub_diag. reflexivity. }
  rewrite {1}/sessp bodies_of_snoc_nl nlines_snoc_nl rest_of_snoc_nl.
  rewrite alt_seq_p_S (alt_seq_p_bs_app ps cs (bodies_of I) [rest_of I]
                         (nlines I) ltac:(rewrite /nlines; lia)).
  rewrite /alt_blk_p Hidx app_nil_r /sessp.
  by rewrite !app_assoc.
Qed.

Lemma sessp_step ps cs I b : sessp ps cs I `prefix_of` sessp ps cs (I ++ [b]).
Proof using.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite sessp_snoc_nl. by eexists.
  - rewrite (sessp_snoc_other ps cs I b Hb). by eexists.
Qed.

Lemma sessp_mono ps cs I I' :
  I `prefix_of` I' -> sessp ps cs I `prefix_of` sessp ps cs I'.
Proof using.
  intros [k ->]. induction k as [| b k IH] using rev_ind.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. etrans; [exact IH | apply sessp_step].
Qed.

Lemma sessp_length_step ps cs I b :
  (length (sessp ps cs I) < length (sessp ps cs (I ++ [b])))%nat.
Proof using.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite sessp_snoc_nl (length_app (sessp ps cs I) _). cbn [length]. lia.
  - rewrite (sessp_snoc_other ps cs I b Hb) (length_app (sessp ps cs I) [b]).
    cbn [length]. lia.
Qed.

Lemma sessp_length_le ps cs I I' :
  I `prefix_of` I' -> (length (sessp ps cs I) <= length (sessp ps cs I'))%nat.
Proof using. intro Hp. exact (prefix_length _ _ (sessp_mono ps cs I I' Hp)). Qed.

Lemma sessp_take ps cs I q :
  (nlines I <= q)%nat -> sessp ps (take q cs) I = sessp ps cs I.
Proof using.
  intros Hq. rewrite /sessp. do 2 f_equal.
  apply alt_seq_p_cs_ext. intros j Hj.
  rewrite list_lookup_total_alt lookup_take; [| lia].
  by rewrite -list_lookup_total_alt.
Qed.

Lemma sessp_ps_ext ps1 ps2 cs I :
  (forall r, (r <= pro_idx_p cs (nlines I))%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  sessp ps1 cs I = sessp ps2 cs I.
Proof using.
  intros Hr. rewrite /sessp (Hr 0%nat ltac:(lia)).
  by rewrite (alt_seq_p_ps_ext ps1 ps2 cs (bodies_of I) (nlines I) Hr).
Qed.

(* the side condition [EchoDisc.pro_ok]/[pro_pin] state, at [palt_panic] *)
Definition pro_ok_p (ps cs : list nat) (q : nat) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps
  /\ (pro_idx_p cs q < pro_rounds ps)%nat.

Global Instance pro_ok_p_dec ps cs q : Decision (pro_ok_p ps cs q).
Proof using. rewrite /pro_ok_p. apply _. Defined.

Lemma pro_ok_p_mono ps cs q q' :
  (q' <= q)%nat -> pro_ok_p ps cs q -> pro_ok_p ps cs q'.
Proof using.
  intros Hq [HF Hlt]. split; [exact HF |].
  pose proof (pro_idx_p_mono cs q' q Hq). lia.
Qed.

Definition pro_pin_p (ps cs : list nat) (I : list (bv 8)) : Prop :=
  forall q, (q < nstarted I)%nat -> (pro_idx_p cs q < pro_rounds ps)%nat.

Lemma pro_pin_p_of_ok ps cs I :
  pro_ok_p ps cs (nlines I) -> pro_pin_p ps cs I.
Proof using.
  intros [_ Hlt] q Hq.
  pose proof (nstarted_le_S I) as H1.
  pose proof (pro_idx_p_mono cs q (nlines I)) as H2.
  destruct (decide (q <= nlines I)%nat) as [Hle | Hgt]; [lia |].
  assert (Hq' : q = nlines I) by lia. lia.
Qed.

(* ====================================================================== *)
(*  5.  THE DISCIPLINE, THE CLAIM, AND THE HISTORY                         *)
(* ====================================================================== *)

(* D3 over one power cycle's input *)
Definition disc_seg_p (seg : list mobs) : Prop := disc_input_p (ins seg).

Global Instance disc_seg_p_dec seg : Decision (disc_seg_p seg).
Proof using. rewrite /disc_seg_p. apply _. Defined.

Lemma disc_seg_p_nil : disc_seg_p [].
Proof using. exact disc_input_p_nil. Qed.

Lemma disc_seg_p_out (seg : list mobs) (b : bv 8) :
  disc_seg_p (seg ++ [ObsUartOut Uart0 b]) <-> disc_seg_p seg.
Proof using. rewrite /disc_seg_p ins_app ins_out app_nil_r. done. Qed.

Lemma disc_seg_p_prefix (seg' seg : list mobs) :
  seg' `prefix_of` seg -> disc_seg_p seg -> disc_seg_p seg'.
Proof using.
  intros [k ->] Hd. rewrite /disc_seg_p ins_app in Hd.
  apply (disc_input_p_prefix _ _ ltac:(by eexists) Hd).
Qed.

(* D1 AT ONE INPUT POSITION, at [EchoDisc.disc_pt]'s statement with
   [sessp] in place of [sess]: the transcript of the input's COMPLETE
   lines ([LineWords.done_of]) is on the wire, so a line may be typed as a
   burst. *)
Definition disc_pt_p (ps cs : list nat) (p : list mobs) : Prop :=
  sessp ps cs (done_of (ins p)) `prefix_of` obs_wire Uart0 p.

Global Instance disc_pt_p_dec ps cs p : Decision (disc_pt_p ps cs p).
Proof using. rewrite /disc_pt_p. apply _. Defined.

(* the per-byte rule implies the per-line one ([EchoDisc.disc_pt_of_strict]) *)
Lemma disc_pt_p_of_strict (ps cs : list nat) (p : list mobs) :
  sessp ps cs (ins p) `prefix_of` obs_wire Uart0 p -> disc_pt_p ps cs p.
Proof using.
  intro H. rewrite /disc_pt_p. etrans; [| exact H].
  apply sessp_mono, done_of_prefix.
Qed.

(* the resolution's range condition, where [EchoDisc]'s was [c < 4]: every
   line's alternative is one ITS SHAPE admits.  [Forall2] also pins the
   length, which [EchoDisc.disc_seg'] states separately. *)
Definition alts_ok_p (I : list (bv 8)) (cs : list nat) : Prop :=
  Forall2 (fun l c => palt_ok l (palt_of c)) (plines_of I) cs.

Global Instance alts_ok_p_dec I cs : Decision (alts_ok_p I cs).
Proof using. rewrite /alts_ok_p. apply _. Defined.

Lemma alts_ok_p_length I cs : alts_ok_p I cs -> length cs = nlines I.
Proof using.
  intro H. apply Forall2_length in H.
  by rewrite /plines_of length_fmap in H.
Qed.

Lemma alts_ok_p_at I cs i :
  alts_ok_p I cs -> (i < nlines I)%nat ->
  palt_ok (pline_of (bodies_of I !!! i)) (palt_at cs i).
Proof using.
  intros H Hi. rewrite /nlines in Hi.
  destruct (lookup_lt_is_Some_2 (bodies_of I) i Hi) as [b Hb].
  assert (Hl : plines_of I !! i = Some (pline_of b))
    by (rewrite /plines_of list_lookup_fmap Hb; reflexivity).
  destruct (Forall2_lookup_l _ _ _ _ _ H Hl) as (c & Hc & Hok).
  rewrite /palt_at (list_lookup_total_correct cs i c Hc).
  by rewrite (list_lookup_total_correct _ _ _ Hb).
Qed.

(* ---- D4: THE COVERED SESSION ENDS AT A FORK-FAILURE ROUND ----------- *)

(* DISCIPLINE RULE D4 (design section 4.3h, owner's ruling "strays" of
   2026-09-21, as REPAIRED by this lane).  A pipeline round whose [fork1]
   failed leaves a STRAY writer alive: it prints a prefix of [dg_execL] at
   any later time, so nothing the session prints after such a round is a
   function of the input any more.  D4 is the premise that stops there:
   A ROUND WHOSE BLOCK IS A SHUFFLE OF THE TWO SOURCES IS THE LAST ROUND
   OF THE COVERED SESSION -- no further line, and no further byte typed.

   IT IS STATED ON THE BYTES ([pmergeable]) AND NOT ON THE ALTERNATIVE,
   and that is the lane's one correction to the ruling.  "The resolution
   has [PForkS] at line [i]" is NOT enough, because the wire does not
   say which alternative ran: at [echo fork | cat] the GOOD run [PRan]
   prints [wl_line ["fork"] ++ u_prompt], which is [alt_forkc] byte for
   byte -- so a user who typed that line, had its [fork1] fail, and
   typed on would be inside a [PRan]-resolved discipline while a stray
   child was still writing, and [pipe_phi] would be FALSE at that trace
   ([d4_ambiguous] in section 8 is the witness).  Reading D4 off the
   BYTES closes that: the [PRan] resolution of such a round is a shuffle
   too, so it ends the covered session as well.  The price is exactly
   the confusable lines, and it is a fact about the WIRE, which is what
   design section 4.3h asks a stray premise to be.

   THE PRICE, MEASURED AND REPORTED: the test is on [pcont] and not on
   the whole block, so it does not read the prologue a PANIC round
   re-enters -- and [alt_panic] ("fork\n") is ITSELF a shuffle prefix.
   So D4 as landed ALSO ends the covered session at sh's main-loop fork
   panic, at either line shape.  That is sound and it is honest ("fork\n"
   on the wire does not say which process wrote it), but it is wider
   than the ruling asks for.  Narrowing it to "the block is a COMPLETE
   fork block" needs the test to read [alt_cont_p] -- the prologue
   included, because a panic followed by a BARE-PROMPT prologue is
   [alt_forkc] byte for byte and the model admits that prologue
   ([pro_alts !!! 0]) -- and then [d4_p] depends on [ps], which
   [PipeDiscDec]'s prologue canonicalisation does not preserve.  A
   ruling is asked for.

   [d4_p] is a [Forall] over [seq] rather than a bounded quantifier so
   that it is decidable and [vm_compute]-able, which is what
   [PipeDiscDec] and the demos of section 8 need. *)
Definition d4_p (cs : list nat) (I : list (bv 8)) : Prop :=
  Forall (fun i => pline_is_pipe (pline_of (bodies_of I !!! i)) = true ->
                   pmergeable (pcont (pline_of (bodies_of I !!! i))
                                 (palt_at cs i)) ->
                   nlines I = S i /\ rest_of I = [])
    (seq 0 (nlines I)).

Global Instance d4_p_dec cs I : Decision (d4_p cs I).
Proof using. rewrite /d4_p. apply _. Defined.

Lemma pd_nlines_nil : nlines [] = 0%nat.
Proof using. by vm_compute. Qed.

Lemma d4_p_at (cs : list nat) (I : list (bv 8)) (i : nat) :
  d4_p cs I -> (i < nlines I)%nat ->
  pline_is_pipe (pline_of (bodies_of I !!! i)) = true ->
  pmergeable (pcont (pline_of (bodies_of I !!! i)) (palt_at cs i)) ->
  nlines I = S i /\ rest_of I = [].
Proof using.
  intros Hd Hi. apply (proj1 (Forall_forall _ _) Hd i).
  apply elem_of_seq. lia.
Qed.

Lemma d4_p_intro (cs : list nat) (I : list (bv 8)) :
  (forall i, (i < nlines I)%nat ->
     pline_is_pipe (pline_of (bodies_of I !!! i)) = true ->
     pmergeable (pcont (pline_of (bodies_of I !!! i)) (palt_at cs i)) ->
     nlines I = S i /\ rest_of I = []) ->
  d4_p cs I.
Proof using.
  intro H. apply Forall_forall. intros i Hi.
  apply elem_of_seq in Hi. apply H. lia.
Qed.

(* THE PER-CYCLE DISCIPLINE, at [EchoDisc.disc_seg']'s shape, with D4 *)
Definition disc_seg_p' (seg : list mobs) : Prop :=
  disc_seg_p seg
  /\ exists ps cs : list nat,
       alts_ok_p (ins seg) cs
       /\ d4_p cs (ins seg)
       /\ forall p : list mobs, p ∈ in_pres seg ->
            pro_ok_p ps cs (nlines (ins p)) /\ disc_pt_p ps cs p.

(* the constructor the literals below spend, [EchoDisc.disc_seg'_intro]'s
   twin.  ([disc_seg_p'] is NOT claimed decidable: the search over the
   resolutions [EchoDisc] can run needs a bound on [sel], and no consumer
   asks for it.) *)
Definition disc_pt_all_p (ps cs : list nat) (seg : list mobs) : Prop :=
  Forall (fun p => pro_ok_p ps cs (nlines (ins p)) /\ disc_pt_p ps cs p)
    (in_pres seg).

Global Instance disc_pt_all_p_dec ps cs seg : Decision (disc_pt_all_p ps cs seg).
Proof using. rewrite /disc_pt_all_p. apply _. Defined.

Lemma disc_seg_p'_intro (seg : list mobs) (ps cs : list nat) :
  disc_seg_p seg -> alts_ok_p (ins seg) cs -> d4_p cs (ins seg) ->
  disc_pt_all_p ps cs seg ->
  disc_seg_p' seg.
Proof using.
  intros Hd Hl Hd4 Hall. split; [exact Hd |]. exists ps, cs.
  split; [exact Hl |]. split; [exact Hd4 |].
  intros p Hp. exact (proj1 (Forall_forall _ _) Hall p Hp).
Qed.

Lemma disc_seg_p'_nil : disc_seg_p' [].
Proof using.
  split; [exact disc_seg_p_nil |]. exists [], [].
  split; [rewrite /alts_ok_p; constructor |].
  split; [apply d4_p_intro; intros i Hi; rewrite /ins /= /nlines in Hi;
          cbn in Hi; lia |].
  intros p Hp. by apply elem_of_nil in Hp.
Qed.

(* THE DISCIPLINE, over the WHOLE history, at [EchoDisc.disc]'s statement *)
Definition disc_p (h : list mobs) : Prop := Forall disc_seg_p' (cycles_of h).

Lemma disc_p_nil : disc_p [].
Proof using. constructor. Qed.

Lemma disc_p_seg h seg : disc_p h -> seg ∈ cycles_of h -> disc_seg_p seg.
Proof using.
  intros Hd Hin. apply elem_of_list_lookup in Hin as [i Hi].
  destruct (Forall_lookup_1 _ _ _ _ Hd Hi) as [Hs _]. exact Hs.
Qed.

(* R3's relation, at the new session *)
Definition expected_rel_p (I out : list (bv 8)) : Prop :=
  exists ps cs : list nat,
    pro_ok_p ps cs (nlines I)
    /\ alts_ok_p I cs
    /\ out `prefix_of` sessp ps cs I.

Lemma expected_rel_p_out_mono I out out' :
  out' `prefix_of` out -> expected_rel_p I out -> expected_rel_p I out'.
Proof using.
  intros Hp (ps & cs & Hok & Hcs & Hout). exists ps, cs.
  split; [exact Hok |]. split; [exact Hcs |]. by etrans.
Qed.

(* THE OUTPUT CLAIM for one power cycle: everything that reached the
   console wire is a PREFIX of the transcript this cycle's input calls
   for, under some resolution.  [EchoDisc.good_out] with [sessp]. *)
Definition good_out_p (seg : list mobs) : Prop :=
  expected_rel_p (ins seg) (obs_wire Uart0 seg).

Lemma good_out_p_nil : good_out_p [].
Proof using.
  exists [0%nat], []. split.
  { split.
    - apply Forall_singleton. rewrite pro_alts_length. lia.
    - vm_compute. lia. }
  split; [rewrite /alts_ok_p; constructor |].
  apply prefix_nil.
Qed.

(* THE THEOREM'S CONCLUSION, at [AppEcho.echo_phi]'s shape with the new
   session and the new discipline.  [App.app_phi] takes the operational
   state as well; this conclusion reads only the trace, so -- as
   [FileDisc.file_phi] does -- the state argument is dropped here and lane
   PIPE-STAGE adds it back at the record's field. *)
Definition pipe_phi (h : list mobs) : Prop :=
  disc_p h -> Forall good_out_p (cycles_of h).

Lemma pipe_phi_nil : pipe_phi [].
Proof using. intros _. rewrite /cycles_of /=. constructor. Qed.

(* ====================================================================== *)
(*  6.  THE ECHO APPLICATION IS THIS ONE AT ITS ECHO LINES                 *)
(*                                                                        *)
(*  Nothing in [EchoDisc] is re-stated or weakened: at a history whose     *)
(*  every complete line is an echo line, [sessp] IS [sess] and [disc_p]    *)
(*  IS [disc] -- which is why the [PEcho] alternatives had to encode as    *)
(*  their own index.                                                       *)
(* ====================================================================== *)

Definition echo_only (I : list (bv 8)) : Prop := Forall body_ok (bodies_of I).

Lemma echo_only_prefix I I' :
  I `prefix_of` I' -> echo_only I' -> echo_only I.
Proof using.
  intros Hp HF. rewrite /echo_only in HF |- *.
  destruct (bodies_of_prefix I I' Hp) as [z Hz].
  rewrite Hz in HF. by apply Forall_app in HF as [? _].
Qed.

Lemma pro_idx_p_echo cs i :
  (forall j, (j < i)%nat -> (cs !!! j < 4)%nat) ->
  pro_idx_p cs i = pro_idx cs i.
Proof using.
  induction i as [| i IH]; intro Hb; [reflexivity |].
  rewrite pro_idx_p_S pro_idx_S IH; [| intros j Hj; apply Hb; lia].
  rewrite /palt_at (palt_panic_echo _ (Hb i ltac:(lia))).
  case_bool_decide as H3; case_decide as H3'; [done | done | done | done].
Qed.

Lemma alt_seq_p_sess ps cs bs q :
  (forall j, (j < q)%nat -> (cs !!! j < 4)%nat) ->
  (forall j, (j < q)%nat -> body_ok (bs !!! j)) ->
  alt_seq_p ps cs bs q = alt_seq ps cs bs q.
Proof using.
  induction q as [| q IH]; intros Hc Hb; [reflexivity |].
  rewrite alt_seq_p_S alt_seq_S IH;
    [| intros j Hj; apply Hc; lia | intros j Hj; apply Hb; lia].
  f_equal. rewrite /alt_blk_p /alt_blk /alt_cont_p /alt_cont.
  rewrite /palt_at (palt_of_lt4 _ (Hc q ltac:(lia)))
          (pline_of_echo _ (Hb q ltac:(lia))).
  rewrite (pro_idx_p_echo cs q ltac:(intros j Hj; apply Hc; lia)).
  change (palt_panic (PEcho (cs !!! q))) with (bool_decide (cs !!! q = 3%nat)).
  assert (Hif : (if bool_decide (cs !!! q = 3%nat)
                 then pro_of (pro_from (S (pro_idx cs q)) ps) else [])
                = (if decide (cs !!! q = 3%nat)
                   then pro_of (pro_from (S (pro_idx cs q)) ps) else []))
    by (case_bool_decide as H3; case_decide as H3'; done).
  rewrite Hif. reflexivity.
Qed.

Lemma sessp_sess ps cs I :
  echo_only I -> (forall j, (j < nlines I)%nat -> (cs !!! j < 4)%nat) ->
  sessp ps cs I = sess ps cs I.
Proof using.
  intros He Hc. rewrite /sessp /sess.
  rewrite (alt_seq_p_sess ps cs (bodies_of I) (nlines I) Hc); [reflexivity |].
  intros j Hj. rewrite /nlines in Hj.
  destruct (lookup_lt_is_Some_2 (bodies_of I) j Hj) as [b Hb].
  rewrite (list_lookup_total_correct _ _ _ Hb).
  exact (Forall_lookup_1 _ _ _ _ He Hb).
Qed.

Lemma pro_ok_p_ok ps cs q :
  (forall j, (j < q)%nat -> (cs !!! j < 4)%nat) ->
  (pro_ok_p ps cs q <-> pro_ok ps cs q).
Proof using.
  intro Hc. rewrite /pro_ok_p /pro_ok (pro_idx_p_echo cs q Hc). done.
Qed.

Lemma alts_ok_p_lt4 I cs :
  echo_only I -> alts_ok_p I cs -> Forall (fun c => (c < 4)%nat) cs.
Proof using.
  intros He Ha. apply Forall_lookup. intros i c Hc.
  destruct (Forall2_lookup_r _ _ _ _ _ Ha Hc) as (l & Hl & Hok).
  rewrite /plines_of list_lookup_fmap in Hl.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
  cbn in Hl. injection Hl as <-.
  rewrite (pline_of_echo b (Forall_lookup_1 _ _ _ _ He Hb)) in Hok.
  exact (palt_ok_echo_lt4 _ c Hok).
Qed.

Lemma alts_ok_p_of_lt4 I cs :
  echo_only I -> length cs = nlines I ->
  Forall (fun c => (c < 4)%nat) cs -> alts_ok_p I cs.
Proof using.
  intros He Hl HF. rewrite /alts_ok_p.
  apply Forall2_same_length_lookup_2;
    [rewrite /plines_of length_fmap; by rewrite Hl |].
  intros i l c Hli Hci.
  rewrite /plines_of list_lookup_fmap in Hli.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
  cbn in Hli. injection Hli as <-.
  rewrite (pline_of_echo b (Forall_lookup_1 _ _ _ _ He Hb)).
  rewrite (palt_of_lt4 c (Forall_lookup_1 _ _ _ _ HF Hci)).
  rewrite /palt_ok. exact (Forall_lookup_1 _ _ _ _ HF Hci).
Qed.

(* THE COMPATIBILITY, at the whole history: a pipeline session that is
   echo-only is disciplined for the echo application too. *)
Lemma disc_p_disc h :
  Forall disc_seg (cycles_of h) -> disc_p h -> disc h.
Proof using.
  intros HD Hf.
  - apply Forall_lookup. intros i seg Hi.
    assert (Hds : disc_seg seg) by (exact (Forall_lookup_1 _ _ _ _ HD Hi)).
    assert (He : echo_only (ins seg)) by (by destruct Hds as (? & _ & _)).
    destruct (Forall_lookup_1 _ _ _ _ Hf Hi)
      as (_ & (ps & cs & Hao & _ & Hall)).
    assert (Hlt4 : Forall (fun c => (c < 4)%nat) cs)
      by (exact (alts_ok_p_lt4 _ _ He Hao)).
    pose proof (alts_ok_p_length _ _ Hao) as Hlen.
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
    assert (Hepd : echo_only (done_of (ins p)))
      by (exact (echo_only_prefix _ _ (done_of_prefix _) Hep)).
    assert (Hc4d : forall j, (j < nlines (done_of (ins p)))%nat ->
                     (cs !!! j < 4)%nat)
      by (rewrite nlines_done; exact Hc4).
    split.
    + by apply (pro_ok_p_ok ps cs (nlines (ins p)) Hc4).
    + rewrite /disc_pt -(sessp_sess ps cs (done_of (ins p)) Hepd Hc4d).
      exact Hpt.
Qed.

(* D4 IS FREE AT AN ECHO-ONLY INPUT: its guard is the line's shape *)
Lemma d4_p_echo (cs : list nat) (I : list (bv 8)) :
  echo_only I -> d4_p cs I.
Proof using.
  intro He. rewrite /d4_p. apply Forall_forall. intros i Hi Hpipe.
  exfalso. apply elem_of_seq in Hi. rewrite /nlines in Hi.
  destruct (lookup_lt_is_Some_2 (bodies_of I) i ltac:(lia)) as [b Hb].
  rewrite (list_lookup_total_correct _ _ _ Hb)
          (pline_of_echo b (Forall_lookup_1 _ _ _ _ He Hb)) in Hpipe.
  discriminate Hpipe.
Qed.

(* ...AND THE CONVERSE: an echo-disciplined history is pipe-disciplined.
   Together with [disc_p_disc] the two disciplines agree at every
   echo-only history, which is what makes the echo application's theorem
   a corollary of this one ([pipe_phi_echo]). *)
Lemma disc_disc_p h :
  Forall disc_seg (cycles_of h) -> disc h -> disc_p h.
Proof using.
  intros HD He. apply Forall_lookup. intros i seg Hi.
  assert (Hds : disc_seg seg) by (exact (Forall_lookup_1 _ _ _ _ HD Hi)).
  assert (Heo : echo_only (ins seg)) by (by destruct Hds as (? & _ & _)).
  destruct (Forall_lookup_1 _ _ _ _ He Hi)
    as (_ & (ps & cs & Hlen & Hlt4 & Hall)).
  split; [exact (disc_input_p_of_disc_input _ Hds) |].
  exists ps, cs. split; [exact (alts_ok_p_of_lt4 _ _ Heo Hlen Hlt4) |].
  split; [exact (d4_p_echo cs (ins seg) Heo) |].
  intros p Hp.
  assert (Hple : ins p `prefix_of` ins seg)
    by (apply ins_prefix;
        exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp)).
  assert (Hep : echo_only (ins p)) by (exact (echo_only_prefix _ _ Hple Heo)).
  assert (Hnl : (nlines (ins p) <= nlines (ins seg))%nat)
    by (by apply nlines_prefix).
  assert (Hc4 : forall j, (j < nlines (ins p))%nat -> (cs !!! j < 4)%nat).
  { intros j Hj.
    destruct (lookup_lt_is_Some_2 cs j ltac:(lia)) as [c Hc].
    rewrite (list_lookup_total_correct _ _ _ Hc).
    exact (Forall_lookup_1 _ _ _ _ Hlt4 Hc). }
  destruct (Hall p Hp) as [Hok Hpt].
  assert (Hepd : echo_only (done_of (ins p)))
    by (exact (echo_only_prefix _ _ (done_of_prefix _) Hep)).
  assert (Hc4d : forall j, (j < nlines (done_of (ins p)))%nat ->
                   (cs !!! j < 4)%nat)
    by (rewrite nlines_done; exact Hc4).
  split.
  + by apply (pro_ok_p_ok ps cs (nlines (ins p)) Hc4).
  + rewrite /disc_pt_p (sessp_sess ps cs (done_of (ins p)) Hepd Hc4d).
    exact Hpt.
Qed.

(* THE CONCLUSION, read back at an echo-only input *)
Lemma expected_rel_p_echo (I out : list (bv 8)) :
  echo_only I -> expected_rel_p I out -> expected_rel I out.
Proof using.
  intros He (ps & cs & Hok & Hao & Hpre).
  pose proof (alts_ok_p_lt4 _ _ He Hao) as Hlt4.
  pose proof (alts_ok_p_length _ _ Hao) as Hlen.
  assert (Hc4 : forall j, (j < nlines I)%nat -> (cs !!! j < 4)%nat).
  { intros j Hj.
    destruct (lookup_lt_is_Some_2 cs j ltac:(lia)) as [c Hc].
    rewrite (list_lookup_total_correct _ _ _ Hc).
    exact (Forall_lookup_1 _ _ _ _ Hlt4 Hc). }
  exists ps, cs.
  split; [by apply (pro_ok_p_ok ps cs (nlines I) Hc4) |].
  split; [exact Hlt4 |].
  rewrite -(sessp_sess ps cs I He Hc4). exact Hpre.
Qed.

Lemma good_out_p_echo (seg : list mobs) :
  echo_only (ins seg) -> good_out_p seg -> good_out seg.
Proof using. exact (expected_rel_p_echo (ins seg) (obs_wire Uart0 seg)). Qed.

(* THE ECHO APPLICATION'S CONCLUSION IS THIS ONE'S, at the echo discipline *)
Lemma pipe_phi_echo (h : list mobs) :
  pipe_phi h -> disc h -> Forall good_out (cycles_of h).
Proof using.
  intros Hp Hd.
  assert (HD : Forall disc_seg (cycles_of h)).
  { eapply Forall_impl; [exact Hd |]. intros seg [Hs _]. exact Hs. }
  pose proof (Hp (disc_disc_p h HD Hd)) as Hg.
  apply Forall_lookup. intros i seg Hi.
  apply (good_out_p_echo seg).
  - destruct (Forall_lookup_1 _ _ _ _ HD Hi) as (Hb & _ & _). exact Hb.
  - exact (Forall_lookup_1 _ _ _ _ Hg Hi).
Qed.

(* ====================================================================== *)
(*  7.  THE LINE MODEL INSTANCE, AND DETERMINACY AS ITS COROLLARY          *)
(*                                                                        *)
(*  [sessp] is [LineModel.lm_sess] at the instance below (state [unit]),   *)
(*  by conversion; the byte shape the determinacy argument reads off this  *)
(*  model is [pcont_panic] and [pcont_shape_nl], and the coverage-ending   *)
(*  arm is [PForkS] with [pmergeable] as what it can have written          *)
(*  ([pmergeable_isforkS], [pmergeable_prefix]).  [sessp_prefix_det] (two  *)
(*  witnesses put the same bytes on the wire) is then                     *)
(*  [LineModel.lm_sess_prefix_det] read back through the equations, with   *)
(*  the discipline's rule D4 as the two guards.  It concludes an equality  *)
(*  of BYTES and never of indices, and it cannot conclude more: at [echo   *)
(*  fork | cat] the good run [PRan] prints exactly what [PFork] prints,    *)
(*  and at [echo exec cat failed | cat] it prints what [PExecR] prints.    *)
(* ====================================================================== *)
Definition pipe_lm : lmodel :=
  MkLM unit pline pline_of palt palt_of palt_panic (fun _ => pcont)
       (fun _ _ _ => tt) (fun _ => palt_ok) pbody_ok pbody_byte pline_ok (fun _ => True)
       palt_isforkS pmergeable.

Lemma pro_idx_p_lm cs i : pro_idx_p cs i = lm_pro_idx pipe_lm cs i.
Proof using. induction i as [| i IH]; [reflexivity |]. cbn. by rewrite IH. Qed.

Lemma alt_cont_p_lm ps cs bs i :
  alt_cont_p ps cs bs i = lm_cont_at pipe_lm ps cs tt bs i.
Proof using. rewrite /alt_cont_p /lm_cont_at pro_idx_p_lm. reflexivity. Qed.

Lemma alt_seq_p_lm ps cs bs q :
  alt_seq_p ps cs bs q = lm_seq pipe_lm ps cs tt bs q.
Proof using. reflexivity. Qed.

Lemma sessp_lm ps cs I : sessp ps cs I = lm_sess pipe_lm ps cs tt I.
Proof using. rewrite /sessp /lm_sess. by rewrite alt_seq_p_lm. Qed.

(* one round's continuation with the prologue it may re-enter, as the
   anti-vacuity demos read it: [LineModel.lm_cont_all] at the instance *)
Definition pcont_all (ps : list nat) (l : pline) (a : palt) : list (bv 8) :=
  pcont l a ++ (if palt_panic a then pro_of (pro_from 1%nat ps) else []).

Lemma pcont_all_lm ps l a : pcont_all ps l a = lm_cont_all pipe_lm ps tt l a.
Proof using. reflexivity. Qed.

Lemma alt_cont_p_0 ps cs bs :
  alt_cont_p ps cs bs 0%nat
  = pcont_all ps (pline_of (bs !!! 0%nat)) (palt_at cs 0%nat).
Proof using. reflexivity. Qed.

Lemma pcont_all_out ps l a :
  palt_panic a = false -> pcont_all ps l a = pcont l a.
Proof using. intro H. rewrite /pcont_all H. by rewrite app_nil_r. Qed.

Lemma alts_ok_p_lm I cs : alts_ok_p I cs <-> lm_alts_ok pipe_lm tt I cs.
Proof using.
  rewrite (lm_alts_ok_nostate pipe_lm tt I cs (fun _ _ _ _ H => H)). reflexivity.
Qed.

Lemma disc_input_p_lm I : disc_input_p I = lm_disc_input pipe_lm I.
Proof using. reflexivity. Qed.

Lemma pro_ok_p_lm ps cs q : pro_ok_p ps cs q <-> lm_pro_ok pipe_lm ps cs q.
Proof using. rewrite /pro_ok_p /lm_pro_ok pro_idx_p_lm. reflexivity. Qed.

Lemma pro_pin_p_lm ps cs I : pro_pin_p ps cs I <-> lm_pro_pin pipe_lm ps cs I.
Proof using.
  rewrite /pro_pin_p /lm_pro_pin. split; intros H q Hq; specialize (H q Hq);
    by rewrite -?pro_idx_p_lm ?pro_idx_p_lm in H |- *.
Qed.

(* ---- the discipline and the claim, as the model's ---- *)
Lemma disc_pt_p_lm ps cs p : disc_pt_p ps cs p <-> lm_disc_pt pipe_lm ps cs tt p.
Proof using. rewrite /disc_pt_p /lm_disc_pt sessp_lm. done. Qed.

(* D4's guard, [pline_is_pipe], IS the model's: only a pipeline line admits
   a coverage-ending arm ([palt_ok_forkS_pipe]), and every pipeline line
   admits one ([palt_ok_forkS_old]) *)
Lemma d4_p_lm cs I : d4_p cs I <-> lm_d4 pipe_lm cs tt I.
Proof using.
  split.
  - intros Hd i Hi (c & Hc & Hf) Hm.
    destruct (palt_isforkS_inv c Hf) as [sel ->].
    exact (d4_p_at cs I i Hd Hi (palt_ok_forkS_pipe _ sel Hc) Hm).
  - intros H. apply d4_p_intro. intros i Hi Hpipe Hm.
    apply (H i Hi); [| exact Hm].
    destruct (pline_of (bodies_of I !!! i)) as [ws | ws] eqn:Hl;
      [discriminate Hpipe |].
    exists (PForkS sel_forkc). split; [| reflexivity].
    change (palt_ok (pline_of (bodies_of I !!! i)) (PForkS sel_forkc)).
    rewrite Hl. exact (palt_ok_forkS_old ws).
Qed.

Lemma disc_seg_p'_lm seg : disc_seg_p' seg <-> lm_disc_seg' pipe_lm tt seg.
Proof using.
  rewrite /disc_seg_p' /lm_disc_seg' /disc_seg_p disc_input_p_lm. split.
  - intros [Hd (ps & cs & Hao & Hd4 & Hall)]. split; [exact Hd |]. exists ps, cs.
    split; [by apply alts_ok_p_lm |]. split; [by apply d4_p_lm |].
    intros p Hp. destruct (Hall p Hp) as [Hok Hpt].
    split; [by apply pro_ok_p_lm | by apply disc_pt_p_lm].
  - intros [Hd (ps & cs & Hao & Hd4 & Hall)]. split; [exact Hd |]. exists ps, cs.
    split; [by apply alts_ok_p_lm |]. split; [by apply d4_p_lm |].
    intros p Hp. destruct (Hall p Hp) as [Hok Hpt].
    split; [by apply pro_ok_p_lm | by apply disc_pt_p_lm].
Qed.

Lemma disc_p_lm h : disc_p h <-> lm_disc pipe_lm h.
Proof using.
  rewrite /disc_p /lm_disc. split; intros H.
  - eapply Forall_impl; [exact H |]. intros seg Hd. exists tt. split; [exact Logic.I | by apply disc_seg_p'_lm].
  - eapply Forall_impl; [exact H |]. intros seg ([] & _ & Hd). by apply disc_seg_p'_lm.
Qed.

Lemma expected_rel_p_lm I out :
  expected_rel_p I out <-> lm_expected_rel pipe_lm tt I out.
Proof using.
  rewrite /expected_rel_p /lm_expected_rel. split.
  - intros (ps & cs & Hok & Hao & Hw). exists ps, cs.
    split; [by apply pro_ok_p_lm |]. split; [by apply alts_ok_p_lm |].
    by rewrite -sessp_lm.
  - intros (ps & cs & Hok & Hao & Hw). exists ps, cs.
    split; [by apply pro_ok_p_lm |]. split; [by apply alts_ok_p_lm |].
    by rewrite sessp_lm.
Qed.

Lemma good_out_p_lm seg : good_out_p seg <-> lm_good_out pipe_lm tt seg.
Proof using. rewrite /good_out_p /lm_good_out. apply expected_rel_p_lm. Qed.

(* the byte shape: what sections 2 and 3 proved of the alternatives *)
Lemma pipe_lm_laws : lm_laws pipe_lm.
Proof using.
  constructor.
  - intros b Hb. exact (proj1 (pbody_ok_line b Hb)).
  - intros s l a _ _ _. exact I.
  - intros s l a H. exact (pcont_panic l a H).
  - intros a H. destruct (palt_isforkS_inv a H) as [sel ->].
    exact (palt_panic_forkS sel).
  - intros s l a _ Ha H. exact (pmergeable_isforkS l a Ha H).
  - intros u' u Hp Hm. exact (pmergeable_prefix u' u Hp Hm).
  - intros s l a _ Hl Ha Hp Hf.
    destruct (pcont_shape_nl l a Hl Ha Hp Hf) as (u & Hu & Hnd & Hnl).
    exists u. split; [exact Hu |]. split; [exact Hnd |].
    intros Y ps W _ Hcmp. apply lm_below_panic_any in Hcmp. destruct Hnl as [Hnl | Hhd].
    + exact (lb_out_eq_panic u Y _ Hnd Hnl Hcmp).
    + exfalso. exact (lb_head_ne_panic u Y _ Hhd Hcmp).
  - intros s l c Hc Ht s'. exists c. split; [exact Hc | exact Ht].
Qed.

Lemma pipe_lm_byte_laws : lm_byte_laws pipe_lm.
Proof using.
  constructor.
  - intros l Hl. exact (pbody_ok_bytes l Hl).
  - intros l Hl. exact (pbody_ok_short l Hl).
  - intros b Hb. destruct Hb as [[Ha | ->] | ->].
    + destruct Ha as [H | [H | H]]; lia.
    + rewrite wl_sp_val. lia.
    + rewrite (_ : bv_unsigned wl_bar = 124%Z); [lia | by vm_compute].
  - change (palt_panic (palt_of 0) = false). by vm_compute.
Qed.

Lemma sessp_prefix_det (ps ps' cs cs' : list nat) (I' I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  pro_ok_p ps' cs' (nlines I') ->
  alts_ok_p I cs -> alts_ok_p I' cs' ->
  pro_pin_p ps cs I -> disc_input_p I -> disc_input_p I' ->
  (forall i, (i < nlines I')%nat -> palt_isforkS (palt_at cs i) = true ->
     (S i = nlines I /\ rest_of I = [])) ->
  (forall i, (i < nlines I')%nat ->
     pline_is_pipe (pline_of (bodies_of I' !!! i)) = true ->
     ~ pmergeable (pcont (pline_of (bodies_of I' !!! i)) (palt_at cs' i))) ->
  sessp ps' cs' I' `prefix_of` sessp ps cs I ->
  I' `prefix_of` I /\ pro_ok_p ps cs (nlines I')
  /\ sessp ps' cs' I' = sessp ps cs I'
  /\ (forall i, (i < nlines I')%nat ->
        alt_cont_p ps' cs' (bodies_of I') i = alt_cont_p ps cs (bodies_of I) i).
Proof using.
  intros Hps Hok Hcs Hcs' Hpin Hd Hd' Hd4 Hnm Hpre.
  rewrite !sessp_lm in Hpre |- *.
  destruct (lm_sess_prefix_det pipe_lm pipe_lm_laws ps ps' cs cs' tt tt I' I Hps
              (proj1 (pro_ok_p_lm _ _ _) Hok)
              (proj1 (alts_ok_p_lm _ _) Hcs) (proj1 (alts_ok_p_lm _ _) Hcs')
              (proj1 (pro_pin_p_lm _ _ _) Hpin) Hd Hd' Logic.I Logic.I Hd4
              ltac:(intros i Hi (c & Hc & Hf) Hm;
                    destruct (palt_isforkS_inv c Hf) as [sel ->];
                    exact (Hnm i Hi (palt_ok_forkS_pipe _ sel Hc) Hm)) Hpre)
    as (H1 & H2 & H3 & H4).
  split; [exact H1 |]. split; [by apply pro_ok_p_lm |].
  split; [exact H3 |].
  intros i Hi. rewrite !alt_cont_p_lm. exact (H4 i Hi).
Qed.

(* ====================================================================== *)
(*  8.  ANTI-VACUITY: SIX MACHINE TRANSCRIPTS, FIVE GOOD AND ONE BAD       *)
(*                                                                        *)
(*  The five good ones say the model admits what the machine does; the     *)
(*  bad one says it does not admit what the machine cannot do -- an        *)
(*  [echo hello | cat] round that prints [goodbye].                        *)
(*                                                                        *)
(*  THE [PBoth] DEMOS CANNOT GO THROUGH [vm_compute], and that is a        *)
(*  fact about [nat] and not about the layout of the code.  The            *)
(*  coordinator's ruling of 2026-09-18 replaced [encode_nat]'s pairing     *)
(*  (~4x per selector entry) with the POSITIONAL/BINARY [bnum] (2x per     *)
(*  entry), which is a factor of about [4 * 10 ^ 9] at the only [|sel|]    *)
(*  the model admits -- and still not enough, because [nat] is UNARY:      *)
(*  [palt_code_both_big] proves the code exceeds [2 ^ 33] at every         *)
(*  admitted interleaving, i.e. a numeral of more than 8.5 thousand        *)
(*  million successors.  No layout escapes it: an injective map out of     *)
(*  the admitted interleavings alone needs values past                     *)
(*  [C(33, 17) > 10 ^ 9].                                                  *)
(*                                                                        *)
(*  MEASURED on the lane's mirror, the round trip                          *)
(*  [bdec (bnum (replicate n true)) = replicate n true] by [vm_compute]:   *)
(*                                                                        *)
(*      n =  8    0.002 s                                                  *)
(*      n = 14    0.012 s                                                  *)
(*      n = 18    0.272 s                                                  *)
(*      n = 22   14.5   s                                                  *)
(*      n = 33   killed at 4 min (extrapolates to hours, and the numeral   *)
(*                itself wants ~275 GB of heap)                            *)
(*                                                                        *)
(*  So the two [PBoth] demos below are proved by REWRITING with            *)
(*  [palt_of_code] ([demo_p_both], one lemma for every interleaving),      *)
(*  which is what the ruling allows and what the stage will have to do     *)
(*  anyway.  Every other demo's code is small (0..9) and computes.         *)
(* ====================================================================== *)

(* ---- the two schedule builders, and what they put on the wire -------- *)

Lemma pd_out_app (l1 l2 : list (bv 8)) :
  demo_out (l1 ++ l2) = demo_out l1 ++ demo_out l2.
Proof using. rewrite /demo_out fmap_app. reflexivity. Qed.

Lemma pd_typed_app (l1 l2 : list (bv 8)) :
  demo_typed (l1 ++ l2) = demo_typed l1 ++ demo_typed l2.
Proof using. rewrite /demo_typed fmap_app join_app. reflexivity. Qed.

Lemma pd_ins_out (l : list (bv 8)) : ins (demo_out l) = [].
Proof using.
  induction l as [| b l IH] using rev_ind; [reflexivity |].
  by rewrite pd_out_app ins_app IH.
Qed.

Lemma pd_wire_out (l : list (bv 8)) : obs_wire Uart0 (demo_out l) = l.
Proof using.
  induction l as [| b l IH] using rev_ind; [reflexivity |].
  rewrite pd_out_app obs_wire_app IH. f_equal; by vm_compute.
Qed.

Lemma pd_ins_typed (l : list (bv 8)) : ins (demo_typed l) = l.
Proof using.
  induction l as [| b l IH] using rev_ind; [reflexivity |].
  rewrite pd_typed_app ins_app IH. f_equal; by vm_compute.
Qed.

Lemma pd_wire_typed (l : list (bv 8)) : obs_wire Uart0 (demo_typed l) = l.
Proof using.
  induction l as [| b l IH] using rev_ind; [reflexivity |].
  rewrite pd_typed_app obs_wire_app IH. f_equal; by vm_compute.
Qed.

(* ---- the ONE-ROUND transcript, with the code never computed ---------- *)

Lemma pd_line_body_nonl (l : pline) :
  pline_ok l -> wl_nl ∉ line_body l.
Proof using.
  intro Hl. pose proof (line_ok_wf _ (pline_ok_ws l Hl)) as Hwf.
  destruct l as [ws | ws]; rewrite /line_body.
  - exact (wl_body_nonl ws Hwf).
  - apply wl_nonl_app; [exact (wl_body_nonl ws Hwf) |].
    apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* the cut of ONE typed line: one body, no remainder *)
Lemma pd_bodies_of_line (l : pline) :
  pline_ok l -> bodies_of (line_bytes l) = [line_body l].
Proof using.
  intro Hl. rewrite /line_bytes bodies_of_snoc_nl
    /bodies_of /rest_of (wl_cut_nonl _ (pd_line_body_nonl l Hl)).
  reflexivity.
Qed.

Lemma pd_rest_of_line (l : pline) : rest_of (line_bytes l) = [].
Proof using. rewrite /line_bytes. exact (rest_of_snoc_nl _). Qed.

Lemma pd_nlines_line (l : pline) : pline_ok l -> nlines (line_bytes l) = 1%nat.
Proof using. intro Hl. by rewrite /nlines (pd_bodies_of_line l Hl). Qed.

(* THE ONE-ROUND TRANSCRIPT.  The alternative's CODE is never computed:
   [palt_of_code] is a rewrite, which is what makes the [PBoth] demos
   possible at all. *)
Lemma sessp_one (ps : list nat) (l : pline) (a : palt) :
  pline_ok l ->
  sessp ps [palt_code a] (line_bytes l)
  = pro_of ps ++ line_body l ++ wl_nl :: pcont_all ps l a.
Proof using.
  intro Hl.
  rewrite /sessp (pd_bodies_of_line l Hl) (pd_nlines_line l Hl)
          (pd_rest_of_line l) app_nil_r.
  rewrite alt_seq_p_S alt_seq_p_0 app_nil_l /alt_blk_p.
  rewrite (_ : [line_body l] !!! 0%nat = line_body l); [| reflexivity].
  do 2 f_equal.
  rewrite alt_cont_p_0 (_ : [line_body l] !!! 0%nat = line_body l);
    [| reflexivity].
  rewrite (pline_of_body l Hl) /palt_at
    (_ : [palt_code a] !!! 0%nat = palt_code a); [| reflexivity].
  by rewrite palt_of_code.
Qed.

(* the three-part schedule the demos are built from: what the user typed
   is the middle part, and the wire is the three parts in order *)
Lemma pd_seg3_ins (a b c : list (bv 8)) :
  ins (demo_out a ++ demo_typed b ++ demo_out c) = b.
Proof using.
  rewrite (ins_app (demo_out a) (demo_typed b ++ demo_out c))
          (ins_app (demo_typed b) (demo_out c))
          (pd_ins_out a) (pd_ins_out c) (pd_ins_typed b).
  by rewrite app_nil_l app_nil_r.
Qed.

Lemma pd_seg3_wire (a b c : list (bv 8)) :
  obs_wire Uart0 (demo_out a ++ demo_typed b ++ demo_out c) = a ++ b ++ c.
Proof using.
  by rewrite (obs_wire_app Uart0 (demo_out a) (demo_typed b ++ demo_out c))
             (obs_wire_app Uart0 (demo_typed b) (demo_out c))
             (pd_wire_out a) (pd_wire_out c) (pd_wire_typed b).
Qed.

(* ---- THE PIPELINE LINE OF THE DEMOS ---------------------------------- *)

Definition pd_ws : list (list (bv 8)) :=
  [sb "echo"%string; sb "hello"%string; sb "world"%string].
Definition pd_l : pline := LPipe pd_ws.
Definition pd_b : list (bv 8) := line_body pd_l.
Definition pd_ran : list (bv 8) := pcont pd_l PRan.

Lemma pd_l_ok : pline_ok pd_l.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma pd_b_val : pd_b = sb "echo hello world | cat"%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* WHAT THE CLAIM SAYS THE CONSOLE SHOWS: the line, then the prompt -- and
   it is the ECHO application's good alternative, byte for byte, because
   cat copies. *)
Lemma pd_ran_val : pd_ran = sb "hello world"%string ++ nlb ++ u_prompt.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma pd_ran_echo : pd_ran = line_alts_of pd_ws !!! 0%nat.
Proof using. reflexivity. Qed.

Lemma pd_plines : plines_of (line_bytes pd_l) = [pd_l].
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- (1) THE SUCCESS TRANSCRIPT -------------------------------------- *)

Definition pd_seg_ran : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes pd_l)
  ++ demo_out pd_ran.

Lemma demo_p_ran : good_out_p pd_seg_ran.
Proof using.
  exists [3%nat; 0%nat], [palt_code PRan].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* ...and the user typed it under the rate discipline, byte by byte *)
Lemma demo_p_ran_disc : disc_seg_p' pd_seg_ran.
Proof using.
  eapply (disc_seg_p'_intro pd_seg_ran [3%nat; 0%nat] [palt_code PRan]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* THE BURST, at both line shapes: the whole line typed with none of it
   echoed yet is disciplined ([EchoDisc.demo_seg_burst]'s twins). *)
Definition pd_seg_burst : list mobs :=
  demo_out u_prologue
  ++ demo_in (line_bytes pd_l)
  ++ demo_out (line_bytes pd_l)
  ++ demo_out pd_ran.

Lemma demo_p_burst_disc : disc_seg_p' pd_seg_burst.
Proof using.
  eapply (disc_seg_p'_intro pd_seg_burst [3%nat; 0%nat] [palt_code PRan]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

Lemma demo_p_burst : good_out_p pd_seg_burst.
Proof using.
  exists [3%nat; 0%nat], [palt_code PRan].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Definition pd_seg_burst_echo : list mobs :=
  demo_out u_prologue
  ++ demo_in (wl_line pd_ws)
  ++ demo_out (wl_line pd_ws)
  ++ demo_out (line_alts_of pd_ws !!! 0%nat).

Lemma demo_p_burst_echo_disc : disc_seg_p' pd_seg_burst_echo.
Proof using.
  eapply (disc_seg_p'_intro pd_seg_burst_echo [3%nat; 0%nat] [0%nat]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

Lemma demo_p_burst_echo : good_out_p pd_seg_burst_echo.
Proof using.
  exists [3%nat; 0%nat], [0%nat].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* ---- (2) THE LEFT EXEC FAILED ---------------------------------------- *)

Definition pd_seg_execL : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes pd_l)
  ++ demo_out alt_execL.

Lemma demo_p_execL : good_out_p pd_seg_execL.
Proof using.
  exists [3%nat; 0%nat], [palt_code PExecL].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* ---- (2b) THE MAIN LOOP'S OWN FORK PANIC, AT A PIPELINE LINE --------- *)

(* The coordinator's ruling of 2026-09-18 in one transcript: the pipeline
   line is typed and echoed, sh's MAIN-loop [fork1] then fails, [panic]
   prints "fork\n" on the console and exits the SHELL, init reaps it and
   its outer loop opens a FRESH PROLOGUE.  Under the design as first
   written no [LPipe] alternative admitted this wire; [PEcho 3] now does,
   and the block is [EchoDisc]'s alternative 3 verbatim. *)
Definition pd_seg_panic : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes pd_l)
  ++ demo_out (alt_panic
               ++ pro_of (pro_from 1%nat [3%nat; 0%nat; 3%nat; 0%nat])).

Lemma demo_p_panic : good_out_p pd_seg_panic.
Proof using.
  exists [3%nat; 0%nat; 3%nat; 0%nat], [palt_code (PEcho 3%nat)].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_p_panic_disc : disc_seg_p' pd_seg_panic.
Proof using.
  eapply (disc_seg_p'_intro pd_seg_panic [3%nat; 0%nat; 3%nat; 0%nat]
            [palt_code (PEcho 3%nat)]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* ...and the wire it puts up is NOT the runcmd child's panic, which ends
   in the prompt: the two part at byte 5.  That is the whole content of
   the hole the ruling closed. *)
Lemma demo_p_panic_ne_forkc :
  alt_panic ++ pro_of (pro_from 1%nat [3%nat; 0%nat; 3%nat; 0%nat])
  <> alt_forkc.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- (2c) THE TERMINAL FORK-FAILURE ROUND, WITH A STRAY BYTE --------- *)

(* THE ROUND THE MODEL WAS CHANGED FOR (lane PIPE-MODEL-3).  [runcmd]'s
   second [fork1] fails while the left child is alive; the left child's
   own [exec /echo] fails too, so it is a STRAY writer.  On the wire: the
   stray's first byte 'e', then the runcmd child's "fork\n" and sh's
   prompt.  No alternative of the OLD model admitted this
   ([PipeForkGap.pfork_execL_gap], now retired); [PForkS] does, at the
   selector that takes one byte from the left source and the rest from
   [alt_forkc]. *)
Definition sel_stray1 : list bool := true :: sel_forkc.

Definition pd_wsf : list (list (bv 8)) :=
  [sb "echo"%string; sb "hello"%string].
Definition pd_lf : pline := LPipe pd_wsf.

Definition pd_fork_blk : list (bv 8) := pcont pd_lf (PForkS sel_stray1).

Lemma pd_fork_blk_val :
  pd_fork_blk = sb "e"%string ++ sb "fork"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Definition pd_seg_fork : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes pd_lf)
  ++ demo_out pd_fork_blk.

Lemma demo_p_fork : good_out_p pd_seg_fork.
Proof using.
  exists [3%nat; 0%nat], [palt_code (PForkS sel_stray1)].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* ...and the user was disciplined up to it: D4 holds because the round
   IS the last one of the segment. *)
Lemma demo_p_fork_disc : disc_seg_p' pd_seg_fork.
Proof using.
  eapply (disc_seg_p'_intro pd_seg_fork [3%nat; 0%nat]
            [palt_code (PForkS sel_stray1)]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* ---- (2d) WHY D4 IS READ OFF THE BYTES AND NOT OFF THE ALTERNATIVE --- *)

(* THE REFUTATION OF THE RULING AS WRITTEN (design section 4.3h: "a
   resolution with [PForkS _] at line [i] has [nlines I = S i]").  At
   this line the GOOD run and the fork failure that took no stray byte
   print THE SAME BYTES, so a resolution that reads the round as [PRan]
   carries no [PForkS] at all, satisfies the alternative-shaped D4
   vacuously, and lets the session go on -- while a stray child is still
   alive and will interleave its diagnostic into a LATER round, which no
   alternative of any later line admits.  [pmergeable] is what both
   readings have in common, and reading D4 off it closes the hole. *)
Definition pd_ws3 : list (list (bv 8)) :=
  [sb "echo"%string; sb "fork"%string].

Lemma d4_ambiguous_bytes :
  pcont (LPipe pd_ws3) PRan = pcont (LPipe pd_ws3) (PForkS sel_forkc).
Proof using.
  rewrite (pcont_forkS_old pd_ws3).
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma d4_ambiguous :
  palt_ok (LPipe pd_ws3) PRan
  /\ palt_isforkS PRan = false
  /\ pmergeable (pcont (LPipe pd_ws3) PRan).
Proof using.
  split; [exact I |]. split; [reflexivity |].
  rewrite d4_ambiguous_bytes.
  exact (pmergeable_forkS (LPipe pd_ws3) sel_forkc
           (palt_ok_forkS_old pd_ws3)).
Qed.

(* ---- (3) AN ECHO ROUND, THEN A PIPELINE ROUND ------------------------ *)

Definition pd_seg_mix : list mobs :=
  demo_out u_prologue
  ++ demo_typed (wl_line demo_ws1)
  ++ demo_out (line_alts_of demo_ws1 !!! 0%nat)
  ++ demo_typed (line_bytes pd_l)
  ++ demo_out pd_ran.

Lemma demo_p_mix : good_out_p pd_seg_mix.
Proof using.
  exists [3%nat; 0%nat], [palt_code (PEcho 0%nat); palt_code PRan].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_p_mix_disc : disc_seg_p' pd_seg_mix.
Proof using.
  eapply (disc_seg_p'_intro pd_seg_mix [3%nat; 0%nat]
            [palt_code (PEcho 0%nat); palt_code PRan]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* ---- (4) AND (5) BOTH EXECS FAILED, AT TWO INTERLEAVINGS ------------- *)

(* the other extreme interleaving: the right child's diagnostic first *)
Definition sel_RL : list bool :=
  replicate (length dg_execR) false ++ replicate (length dg_execL) true.

Lemma sel_RL_ok ws : palt_ok (LPipe ws) (PBoth sel_RL).
Proof using.
  rewrite /palt_ok /sel_RL. split.
  - rewrite length_app !length_replicate. lia.
  - rewrite count_true_app count_true_replicate_false
            count_true_replicate_true. lia.
Qed.

Lemma pmerge_sel_RL : pmerge sel_RL dg_execL dg_execR = dg_execR ++ dg_execL.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Definition pd_seg_both (c : list (bv 8)) : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes pd_l)
  ++ demo_out (c ++ u_prompt).

(* ONE LEMMA FOR EVERY INTERLEAVING, with the code never computed *)
Lemma demo_p_both (sel : list bool) (c : list (bv 8)) :
  palt_ok pd_l (PBoth sel) -> pmerge sel dg_execL dg_execR = c ->
  good_out_p (pd_seg_both c).
Proof using.
  intros Hok Hm.
  pose proof (pd_seg3_ins u_prologue (line_bytes pd_l) (c ++ u_prompt))
    as Hins.
  pose proof (pd_seg3_wire u_prologue (line_bytes pd_l) (c ++ u_prompt))
    as Hw.
  rewrite -/(pd_seg_both c) in Hins, Hw.
  exists [3%nat; 0%nat], [palt_code (PBoth sel)].
  rewrite Hins Hw. split.
  { split.
    - apply (bool_decide_unpack _). vm_compute. exact I.
    - rewrite (pd_nlines_line pd_l pd_l_ok) pro_idx_p_S /palt_at
        (_ : [palt_code (PBoth sel)] !!! 0%nat = palt_code (PBoth sel));
        [| reflexivity].
      rewrite palt_of_code. cbn [pro_idx_p palt_panic]. vm_compute. lia. }
  split.
  { rewrite /alts_ok_p pd_plines. constructor; [| constructor].
    by rewrite palt_of_code. }
  rewrite (sessp_one [3%nat; 0%nat] pd_l (PBoth sel) pd_l_ok).
  rewrite (pcont_all_out _ pd_l (PBoth sel) ltac:(reflexivity)).
  rewrite /pcont Hm pro_of_good /line_bytes -!app_assoc. reflexivity.
Qed.

Lemma demo_p_both_LR : good_out_p (pd_seg_both (dg_execL ++ dg_execR)).
Proof using.
  apply (demo_p_both sel_LR); [apply sel_LR_ok | exact pmerge_sel_LR].
Qed.

Lemma demo_p_both_RL : good_out_p (pd_seg_both (dg_execR ++ dg_execL)).
Proof using.
  apply (demo_p_both sel_RL); [apply sel_RL_ok | exact pmerge_sel_RL].
Qed.

(* the two wires really are different, so the model's [PBoth] arm is not
   a single alternative in disguise *)
Lemma demo_p_both_distinct : dg_execL ++ dg_execR <> dg_execR ++ dg_execL.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- THE EXTENSION IS REAL, AT THE BAR ------------------------------- *)

(* [pbody_byte] is not decoration: the user typing [echo hello world | cat]
   is MID-LINE at [echo hello world |], whose last byte [EchoDisc]'s
   [wl_body_byte] refutes -- so the echo model's D3 rejects both the
   partial line and the complete one, and this model accepts both. *)
Lemma demo_p_partial : disc_input_p (sb "echo hello world |"%string).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma demo_p_partial_not_echo :
  ~ disc_input (sb "echo hello world |"%string).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma demo_p_full : disc_input_p (line_bytes pd_l).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma demo_p_full_not_echo : ~ disc_input (line_bytes pd_l).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- (6) THE NEGATIVE WITNESS ---------------------------------------- *)

(* the head byte of a concatenation is the head byte of its first part *)
Lemma pd_head_app (C Z : list (bv 8)) (b c : bv 8) :
  C !! 0%nat = Some c -> (C ++ Z) !! 0%nat = Some b -> b = c.
Proof using.
  intros Hc Hb. rewrite (lookup_app_l C Z 0%nat) in Hb.
  - rewrite Hc in Hb. by injection Hb.
  - apply lookup_lt_Some in Hc. lia.
Qed.

Definition pd_ws2 : list (list (bv 8)) :=
  [sb "echo"%string; sb "hello"%string].
Definition pd_l2 : pline := LPipe pd_ws2.
Definition pd_b2 : list (bv 8) := line_body pd_l2.

Lemma pd_l2_ok : pline_ok pd_l2.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma pd_b2_val : pd_b2 = sb "echo hello | cat"%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma pd_line_bytes2 : line_bytes pd_l2 = pd_b2 ++ [wl_nl].
Proof using. reflexivity. Qed.

(* WHAT AN [echo hello | cat] ROUND CAN PUT ON THE WIRE FIRST: 'h', 'e',
   'p', 'f' or '$'.  NEVER 'g'. *)
Lemma pd_bad_head (a : palt) (Z : list (bv 8)) (b : bv 8) :
  palt_ok pd_l2 a ->
  (pcont pd_l2 a ++ Z) !! 0%nat = Some b -> bv_unsigned b <> 103%Z.
Proof using.
  intros Ha Hb.
  assert (HeL : dg_execL !! 0%nat = Some (Z_to_bv 8 101%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HeR : dg_execR !! 0%nat = Some (Z_to_bv 8 101%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hran : (wl_line (drop 1 (pline_ws pd_l2)) ++ u_prompt) !! 0%nat
                 = Some (Z_to_bv 8 104%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HxL : alt_execL !! 0%nat = Some (Z_to_bv 8 101%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HxR : alt_execR !! 0%nat = Some (Z_to_bv 8 101%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hpi : alt_pipe !! 0%nat = Some (Z_to_bv 8 112%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hfk : alt_forkc !! 0%nat = Some (Z_to_bv 8 102%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  destruct a as [k | | | | sel | | sel |]; rewrite /pcont in Hb.
  - (* the MAIN loop's own fork panic, which a pipeline line now admits *)
    assert (Hk : k = 3%nat) by (exact Ha).
    rewrite Hk (line_alts_of_3 (pline_ws pd_l2)) in Hb.
    rewrite (pd_head_app _ _ _ _ alt_panic_head Hb). by vm_compute.
  - rewrite (pd_head_app _ _ _ _ Hran Hb). by vm_compute.
  - rewrite (pd_head_app _ _ _ _ HxL Hb). by vm_compute.
  - rewrite (pd_head_app _ _ _ _ HxR Hb). by vm_compute.
  - (* both execs failed: the interleaving's first byte is one of the two
       diagnostics' first bytes, and they are both 'e' *)
    destruct (pmerge sel dg_execL dg_execR) as [| x r] eqn:Hm.
    + rewrite app_nil_l in Hb.
      rewrite (pd_head_app _ _ _ _ u_prompt_head Hb). by vm_compute.
    + assert (Hc : ((x :: r) ++ u_prompt) !! 0%nat = Some x)
        by reflexivity.
      rewrite (pd_head_app _ _ _ _ Hc Hb).
      assert (Hmx : pmerge sel dg_execL dg_execR !! 0%nat = Some x)
        by (rewrite Hm; reflexivity).
      destruct (pmerge_head sel dg_execL dg_execR x Hmx) as [H | H].
      * rewrite HeL in H. injection H as Hx. rewrite -Hx. by vm_compute.
      * rewrite HeR in H. injection H as Hx. rewrite -Hx. by vm_compute.
  - rewrite (pd_head_app _ _ _ _ Hpi Hb). by vm_compute.
  - (* the terminal fork-failure round: the block's first byte comes from
       the stray's diagnostic ('e') or from sh's panic line ('f') *)
    destruct Ha as (Hne & H1 & H2).
    assert (Hml : length (pmerge sel dg_execL alt_forkc) = length sel)
      by (by apply pmerge_length).
    destruct (pmerge sel dg_execL alt_forkc) as [| x r] eqn:Hm.
    { exfalso. cbn [length] in Hml.
      destruct sel as [| z sel']; [by destruct (Hne eq_refl) |].
      cbn [length] in Hml. lia. }
    assert (Hc : (x :: r) !! 0%nat = Some x) by reflexivity.
    rewrite (pd_head_app _ _ _ _ Hc Hb).
    assert (Hmx : pmerge sel dg_execL alt_forkc !! 0%nat = Some x)
      by (rewrite Hm; reflexivity).
    destruct (pmerge_head sel dg_execL alt_forkc x Hmx) as [H | H].
    + rewrite HeL in H. injection H as Hx. rewrite -Hx. by vm_compute.
    + rewrite Hfk in H. injection H as Hx. rewrite -Hx. by vm_compute.
  - rewrite (pd_head_app _ _ _ _ u_prompt_head Hb). by vm_compute.
Qed.

(* the cancellation the refutation goes through *)
Lemma pd_cancel (A B G C : list (bv 8)) :
  (A ++ (B ++ [wl_nl]) ++ G) `prefix_of` (A ++ ((B ++ wl_nl :: C) ++ [])) ->
  G `prefix_of` C.
Proof using.
  intro Hp. rewrite app_nil_r -!app_assoc in Hp.
  apply wl_prefix_app_cancel in Hp.
  apply wl_prefix_app_cancel in Hp.
  exact (prefix_cons_inv_2 _ _ _ _ Hp).
Qed.

(* THE WIRE THAT IS NOT ADMITTED: [echo hello | cat] was typed, and the
   console printed [goodbye].  Nothing the model admits prints a byte
   nobody sent through the pipe, and the refutation is the determinacy
   theorem plus one head byte. *)
Definition pd_bad_out : list (bv 8) := sb "goodbye"%string ++ nlb ++ u_prompt.

Definition pd_seg_bad : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes pd_l2)
  ++ demo_out pd_bad_out.

Lemma demo_p_bad : ~ good_out_p pd_seg_bad.
Proof using.
  intros (ps & cs & Hok & Hcs & Hpre).
  pose proof (pd_seg3_ins u_prologue (line_bytes pd_l2) pd_bad_out) as Hins.
  pose proof (pd_seg3_wire u_prologue (line_bytes pd_l2) pd_bad_out) as Hw.
  rewrite -/pd_seg_bad in Hins, Hw.
  (* the honest transcript through the EMPTY input is already on the wire *)
  assert (HT : sessp [3%nat; 0%nat] [] [] `prefix_of` sessp ps cs (ins pd_seg_bad)).
  { etrans; [| exact Hpre]. rewrite Hw sessp_nil pro_of_good. by eexists. }
  destruct (sessp_prefix_det ps [3%nat; 0%nat] cs [] [] (ins pd_seg_bad)
              (proj1 Hok)
              ltac:(split;
                    [apply (bool_decide_unpack _); vm_compute; exact I
                    | vm_compute; lia])
              Hcs
              ltac:(rewrite /alts_ok_p; constructor)
              (pro_pin_p_of_ok ps cs (ins pd_seg_bad) Hok)
              ltac:(rewrite Hins; apply (bool_decide_unpack _);
                    vm_compute; exact I)
              disc_input_p_nil
              ltac:(intros i Hi; rewrite pd_nlines_nil in Hi; lia)
              ltac:(intros i Hi; rewrite pd_nlines_nil in Hi; lia)
              HT)
    as (_ & _ & Heq & _).
  rewrite !sessp_nil pro_of_good in Heq.
  (* so the adversary's prologue IS init's banner and sh's first prompt *)
  rewrite Hw Hins in Hpre.
  rewrite /sessp -Heq (pd_bodies_of_line pd_l2 pd_l2_ok)
          (pd_nlines_line pd_l2 pd_l2_ok) (pd_rest_of_line pd_l2) in Hpre.
  rewrite alt_seq_p_S alt_seq_p_0 app_nil_l /alt_blk_p
          (_ : [pd_b2] !!! 0%nat = pd_b2) in Hpre; [| reflexivity].
  rewrite pd_line_bytes2 in Hpre.
  apply pd_cancel in Hpre.
  (* the round's first byte would have to be 'g' *)
  assert (Hg : pd_bad_out !! 0%nat = Some (Z_to_bv 8 103%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HC : alt_cont_p ps cs [pd_b2] 0%nat !! 0%nat
               = Some (Z_to_bv 8 103%Z))
    by (eapply lb_prefix_lookup; [exact Hpre | exact Hg]).
  (* ...but the round's alternative is one a pipeline line admits, and no
     such alternative re-enters the prologue, so the block IS its output *)
  assert (Ha0 : palt_ok pd_l2 (palt_at cs 0%nat)).
  { pose proof (alts_ok_p_at (ins pd_seg_bad) cs 0%nat Hcs
                  ltac:(rewrite Hins (pd_nlines_line pd_l2 pd_l2_ok); lia))
      as H.
    rewrite Hins (pd_bodies_of_line pd_l2 pd_l2_ok)
            (_ : [pd_b2] !!! 0%nat = pd_b2) in H; [| reflexivity].
    by rewrite (pline_of_body pd_l2 pd_l2_ok) in H. }
  rewrite /alt_cont_p (_ : [pd_b2] !!! 0%nat = pd_b2) in HC; [| reflexivity].
  rewrite (pline_of_body pd_l2 pd_l2_ok) in HC.
  pose proof (pd_bad_head (palt_at cs 0%nat) _ _ Ha0 HC) as Hne.
  apply Hne. by vm_compute.
Qed.

(* ====================================================================== *)
(*  9.  THE ASSUMPTION CHECK                                              *)
(*                                                                        *)
(*  This file is Iris-free and axiom-free.  The tree's audit convention    *)
(*  is a descoped [*Assumptions.v] beside the theorem it audits; a pure    *)
(*  model has no theorem of its own to audit, so the check is recorded     *)
(*  here and re-run by pasting these lines at the end of the file.  All    *)
(*  thirteen print exactly "Closed under the global context" (checked      *)
(*  2026-09-18 on the lane's mirror, after the coordinator's two           *)
(*  rulings):                                                              *)
(*                                                                        *)
(*    Print Assumptions bdec_bnum.                                         *)
(*    Print Assumptions palt_of_code.                                      *)
(*    Print Assumptions palt_code_inj.                                     *)
(*    Print Assumptions palt_code_both_big.                                *)
(*    Print Assumptions pmerge_prefix.                                     *)
(*    Print Assumptions pcont_shape.                                       *)
(*    Print Assumptions pcont_shape_nl.                                    *)
(*    Print Assumptions sessp_prefix_det.                                  *)
(*    Print Assumptions disc_p_disc.                                       *)
(*    Print Assumptions demo_p_ran.                                        *)
(*    Print Assumptions demo_p_panic.                                      *)
(*    Print Assumptions demo_p_both_LR.                                    *)
(*    Print Assumptions demo_p_bad.                                        *)
(* ====================================================================== *)
