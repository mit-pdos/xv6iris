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

(* D3: every COMPLETE body parses to an admissible line, and the partial
   line is body bytes -- '|' included -- short enough that its newline
   still fits [getcmd]'s buffer. *)
Definition disc_input_p (I : list (bv 8)) : Prop :=
  Forall pbody_ok (bodies_of I)
  /\ Forall pbody_byte (rest_of I)
  /\ (S (length (rest_of I)) < line_max)%nat.

Global Instance disc_input_p_dec I : Decision (disc_input_p I).
Proof using. rewrite /disc_input_p. apply _. Defined.

Lemma disc_input_p_body I i b :
  disc_input_p I -> bodies_of I !! i = Some b -> pbody_ok b.
Proof using. intros (Hb & _ & _) Hi. exact (Forall_lookup_1 _ _ _ _ Hb Hi). Qed.

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

(* THE TWO DIAGNOSTICS THAT CAN COLLIDE ON THE WIRE, as raw bytes: the
   left child's (echo could not be exec'd) and the right child's (cat
   could not be).  [dg_execL] is [EchoDisc.dg_exec]'s line on the nose,
   which is why an [LEcho] round and an [LPipe] round print the SAME bytes
   when their left exec fails. *)
Definition dg_execL : list (bv 8) := wl_line dg_exec.
Definition dg_execR : list (bv 8) := wl_line dg_exec_cat.

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

Lemma pmerge_true_cons s b d1 d2 :
  pmerge (true :: s) (b :: d1) d2 = b :: pmerge s d1 d2.
Proof using. reflexivity. Qed.

Lemma pmerge_false_cons s d1 b d2 :
  pmerge (false :: s) d1 (b :: d2) = b :: pmerge s d1 d2.
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

(* ---- THE TERMINAL ROUND'S ALTERNATIVE, AND THE OLD [PFork] ---------- *)

(* the one-bit reading every consumer takes: IS this round the terminal
   fork-failure one? *)
Definition palt_isforkS (a : palt) : bool :=
  match a with PForkS _ => true | _ => false end.

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
   stage's [PipeOutPure.pend2 R sel] is [pmerge sel dg_execL R] and the
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

Lemma pro_idx_p_ext cs1 cs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  forall j, (j <= q)%nat -> pro_idx_p cs1 j = pro_idx_p cs2 j.
Proof using.
  intros Hj j. induction j as [| j IH]; intros Hjq; [done |].
  rewrite !pro_idx_p_S IH; [| lia].
  by rewrite /palt_at (Hj j ltac:(lia)).
Qed.

Lemma alt_seq_p_S ps cs bs q :
  alt_seq_p ps cs bs (S q) = alt_seq_p ps cs bs q ++ alt_blk_p ps cs bs q.
Proof using.
  rewrite /alt_seq_p List.seq_S fmap_app concat_app Nat.add_0_l /=.
  by rewrite app_nil_r.
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

Lemma alt_seq_p_ps_ext ps1 ps2 cs bs q :
  (forall r, (r <= pro_idx_p cs q)%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_seq_p ps1 cs bs q = alt_seq_p ps2 cs bs q.
Proof using. intro Hr. by apply (alt_seq_p_ext ps1 ps2 cs cs bs bs q). Qed.

Lemma sessp_length ps cs I :
  length (sessp ps cs I)
  = (length (pro_of ps) + length (alt_seq_p ps cs (bodies_of I) (nlines I))
     + length (rest_of I))%nat.
Proof using.
  rewrite /sessp (length_app (pro_of ps) _)
    (length_app (alt_seq_p ps cs (bodies_of I) (nlines I)) (rest_of I)). lia.
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

Definition pro_pin_p (ps cs : list nat) (I : list (bv 8)) : Prop :=
  forall q, (q < nstarted I)%nat -> (pro_idx_p cs q < pro_rounds ps)%nat.

(* ====================================================================== *)
(*  5.  THE DISCIPLINE, THE CLAIM, AND THE HISTORY                         *)
(* ====================================================================== *)

(* D3 over one power cycle's input *)
Definition disc_seg_p (seg : list mobs) : Prop := disc_input_p (ins seg).

Global Instance disc_seg_p_dec seg : Decision (disc_seg_p seg).
Proof using. rewrite /disc_seg_p. apply _. Defined.

(* D1 AT ONE INPUT POSITION, at [EchoDisc.disc_pt]'s statement with
   [sessp] in place of [sess]: the transcript of the input's COMPLETE
   lines ([LineWords.done_of]) is on the wire, so a line may be typed as a
   burst. *)
Definition disc_pt_p (ps cs : list nat) (p : list mobs) : Prop :=
  sessp ps cs (done_of (ins p)) `prefix_of` obs_wire Uart0 p.

Global Instance disc_pt_p_dec ps cs p : Decision (disc_pt_p ps cs p).
Proof using. rewrite /disc_pt_p. apply _. Defined.

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

Lemma d4_p_at (cs : list nat) (I : list (bv 8)) (i : nat) :
  d4_p cs I -> (i < nlines I)%nat ->
  pline_is_pipe (pline_of (bodies_of I !!! i)) = true ->
  pmergeable (pcont (pline_of (bodies_of I !!! i)) (palt_at cs i)) ->
  nlines I = S i /\ rest_of I = [].
Proof using.
  intros Hd Hi. apply (proj1 (Forall_forall _ _) Hd i).
  apply elem_of_seq. lia.
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

(* THE DISCIPLINE, over the WHOLE history, at [EchoDisc.disc]'s statement *)
Definition disc_p (h : list mobs) : Prop := Forall disc_seg_p' (cycles_of h).

(* R3's relation, at the new session *)
Definition expected_rel_p (I out : list (bv 8)) : Prop :=
  exists ps cs : list nat,
    pro_ok_p ps cs (nlines I)
    /\ alts_ok_p I cs
    /\ out `prefix_of` sessp ps cs I.

(* THE OUTPUT CLAIM for one power cycle: everything that reached the
   console wire is a PREFIX of the transcript this cycle's input calls
   for, under some resolution.  [EchoDisc.good_out] with [sessp]. *)
Definition good_out_p (seg : list mobs) : Prop :=
  expected_rel_p (ins seg) (obs_wire Uart0 seg).

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

Lemma alt_seq_p_lm ps cs bs q :
  alt_seq_p ps cs bs q = lm_seq pipe_lm ps cs tt bs q.
Proof using. reflexivity. Qed.

Lemma sessp_lm ps cs I : sessp ps cs I = lm_sess pipe_lm ps cs tt I.
Proof using. rewrite /sessp /lm_sess. by rewrite alt_seq_p_lm. Qed.

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

(* ===================================================================== *)
(*  THE DISCIPLINE IS DECIDABLE (was [PipeDisc.v] until union cut C9h) *)
(* ===================================================================== *)
From stdpp Require Import list_numbers.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(* ====================================================================== *)
(*  0.  ONE SMALL LIST FACT                                                *)
(* ====================================================================== *)

(* the out-of-range reading of [!!!] is [0], so a pointwise map that fixes
   [0] commutes with it *)
Lemma pdd_lookup_total_fmap (f : nat -> nat) (l : list nat) (i : nat) :
  f 0%nat = 0%nat -> (f <$> l) !!! i = f (l !!! i).
Proof using.
  intro Hf. rewrite !list_lookup_total_alt list_lookup_fmap.
  destruct (l !! i) as [x |]; cbn; [reflexivity | by rewrite Hf].
Qed.

Ltac pdd_elem :=
  solve [ repeat first [ apply elem_of_list_here | apply elem_of_list_further ] ].

(* ====================================================================== *)
(*  1.  THE INTERLEAVINGS ONE [PBoth] ROUND ADMITS                         *)
(* ====================================================================== *)

(* EVERY SELECTOR OF LENGTH [n] WITH EXACTLY [k] [true]s, by recursion on
   the first entry.  At the one length the model admits this list has
   [C(33,17) > 10^9] entries: it is DEFINED so that the search space is
   finite and its membership law is PROVED, and it is never run. *)
Fixpoint choose (n k : nat) : list (list bool) :=
  match n with
  | 0%nat => if decide (k = 0%nat) then [[]] else []
  | S n' =>
      ((fun s => false :: s) <$> choose n' k)
      ++ (match k with
          | 0%nat => []
          | S k' => (fun s => true :: s) <$> choose n' k'
          end)
  end.

Lemma elem_of_choose (n k : nat) (sel : list bool) :
  sel ∈ choose n k <-> length sel = n /\ count_true sel = k.
Proof using.
  revert k sel. induction n as [| n IH]; intros k sel; cbn [choose].
  - case_decide as Hk.
    + rewrite elem_of_list_singleton. split.
      * intros ->. cbn [length count_true]. split; [reflexivity | lia].
      * intros [Hl _]. by apply nil_length_inv in Hl.
    + rewrite elem_of_nil. split; [done |].
      intros [Hl Hc]. apply nil_length_inv in Hl as ->.
      cbn [count_true] in Hc. lia.
  - rewrite elem_of_app. split.
    + intros [Hin | Hin].
      * apply elem_of_list_fmap in Hin as (s & -> & Hs).
        apply IH in Hs as [Hl Hc]. cbn [length count_true]. split; lia.
      * destruct k as [| k']; [by apply elem_of_nil in Hin |].
        apply elem_of_list_fmap in Hin as (s & -> & Hs).
        apply IH in Hs as [Hl Hc]. cbn [length count_true]. split; lia.
    + intros [Hl Hc]. destruct sel as [| b s]; [cbn [length] in Hl; lia |].
      cbn [length] in Hl. destruct b; cbn [count_true] in Hc.
      * destruct k as [| k']; [lia |]. right.
        apply elem_of_list_fmap. exists s. split; [reflexivity |].
        apply IH. split; lia.
      * left. apply elem_of_list_fmap. exists s. split; [reflexivity |].
        apply IH. split; lia.
Qed.

(* ---- EVERY SELECTOR THE TERMINAL ROUND ADMITS ------------------------ *)

(* [PForkS]'s selector is NOT of one fixed length: the stray writes
   anything from nothing to the whole of [dg_execL] and the fork round
   writes anything from one byte to the whole of [alt_forkc].  So the
   enumerator is every list of booleans up to [|dg_execL| + |alt_forkc|]
   = 24 entries, filtered by [palt_ok].  Like the [PBoth] branch it is a
   THEOREM's enumerator and not a program's: 2^24 entries, none of which
   any proof evaluates. *)
Lemma pdd_elem_of_concat {A} (x : A) (ls : list (list A)) :
  x ∈ concat ls <-> exists l, l ∈ ls /\ x ∈ l.
Proof using.
  induction ls as [| l ls IH]; cbn [concat].
  - split; [intro H; by apply elem_of_nil in H |].
    intros (l & Hl & _). by apply elem_of_nil in Hl.
  - rewrite elem_of_app IH. split.
    + intros [H | (l' & Hl' & Hx)].
      * exists l. split; [apply elem_of_list_here | exact H].
      * exists l'. split; [by apply elem_of_list_further | exact Hx].
    + intros (l' & Hl' & Hx). apply elem_of_cons in Hl' as [-> | Hl'].
      * by left.
      * right. by exists l'.
Qed.

Definition sels_len (n : nat) : list (list bool) :=
  concat ((fun k => choose n k) <$> seq 0 (S n)).

Lemma elem_of_sels_len (n : nat) (sel : list bool) :
  sel ∈ sels_len n <-> length sel = n.
Proof using.
  rewrite /sels_len pdd_elem_of_concat. split.
  - intros (l & Hl & Hx). apply elem_of_list_fmap in Hl as (k & -> & _).
    exact (proj1 (proj1 (elem_of_choose n k sel) Hx)).
  - intro Hlen. exists (choose n (count_true sel)). split.
    + apply elem_of_list_fmap. exists (count_true sel).
      split; [reflexivity |]. apply elem_of_seq.
      pose proof (count_true_le sel). lia.
    + apply elem_of_choose. split; [exact Hlen | reflexivity].
Qed.

Definition all_sels (n : nat) : list (list bool) :=
  concat (sels_len <$> seq 0 (S n)).

Lemma elem_of_all_sels (n : nat) (sel : list bool) :
  sel ∈ all_sels n <-> (length sel <= n)%nat.
Proof using.
  rewrite /all_sels pdd_elem_of_concat. split.
  - intros (l & Hl & Hx). apply elem_of_list_fmap in Hl as (m & -> & Hm).
    apply elem_of_seq in Hm. apply elem_of_sels_len in Hx. lia.
  - intro Hle. exists (sels_len (length sel)). split.
    + apply elem_of_list_fmap. exists (length sel).
      split; [reflexivity |]. apply elem_of_seq. lia.
    + by apply elem_of_sels_len.
Qed.

Definition forkS_sels : list (list bool) :=
  List.filter (fun sel => bool_decide (palt_ok (LPipe []) (PForkS sel)))
    (all_sels (length dg_execL + length alt_forkc)).

Lemma elem_of_forkS_sels (ws : list (list (bv 8))) (sel : list bool) :
  sel ∈ forkS_sels <-> palt_ok (LPipe ws) (PForkS sel).
Proof using.
  rewrite /forkS_sels elem_of_list_In filter_In -elem_of_list_In. split.
  - intros [_ Hb]. apply bool_decide_eq_true in Hb. exact Hb.
  - intro Hok. split.
    + apply elem_of_all_sels.
      destruct Hok as (_ & H1 & H2).
      pose proof (count_true_le sel). lia.
    + by apply bool_decide_eq_true.
Qed.

(* ====================================================================== *)
(*  2.  THE CODES ONE LINE ADMITS                                          *)
(* ====================================================================== *)

Definition palt_fix_cands (l : pline) : list palt :=
  match l with
  | LEcho _ => [PEcho 0%nat; PEcho 1%nat; PEcho 2%nat; PEcho 3%nat]
  | LPipe _ => [PEcho 3%nat; PRan; PExecL; PExecR; PPipe; PSilent]
  end.

(* the CANONICAL codes of the alternatives one line shape admits: the
   constant ones, and -- at a pipeline line -- one per admitted
   interleaving *)
Definition palt_cands (l : pline) : list nat :=
  (palt_code <$> palt_fix_cands l)
  ++ match l with
     | LEcho _ => []
     | LPipe _ =>
         ((fun sel => palt_code (PBoth sel))
            <$> choose (length dg_execL + length dg_execR) (length dg_execL))
         ++ ((fun sel => palt_code (PForkS sel)) <$> forkS_sels)
     end.

Lemma palt_fix_cands_ok l : Forall (palt_ok l) (palt_fix_cands l).
Proof using.
  destruct l as [ws | ws]; cbn [palt_fix_cands].
  - repeat (constructor; [cbn [palt_ok]; lia |]). constructor.
  - constructor; [reflexivity |].
    repeat (constructor; [exact I |]). constructor.
Qed.

(* COMPLETENESS: every alternative a line admits has its code in the
   list.  This is what keeps the decision procedure from being vacuously
   "no" -- and, with [palt_cands_both_LR] below, what says the [PBoth]
   branch of the enumerator is not empty. *)
Lemma palt_cands_alt l a : palt_ok l a -> palt_code a ∈ palt_cands l.
Proof using.
  intro H. rewrite /palt_cands elem_of_app.
  destruct l as [ws | ws]; destruct a as [k | | | | sel | | sel |];
    cbn [palt_ok] in H; try done.
  - left. apply elem_of_list_fmap. exists (PEcho k). split; [reflexivity |].
    cbn [palt_fix_cands].
    assert (Hk : k = 0%nat \/ k = 1%nat \/ k = 2%nat \/ k = 3%nat) by lia.
    destruct Hk as [-> | [-> | [-> | ->]]]; pdd_elem.
  - left. apply elem_of_list_fmap. exists (PEcho k). split; [reflexivity |].
    rewrite H. cbn [palt_fix_cands]. pdd_elem.
  - left. apply elem_of_list_fmap. exists PRan. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - left. apply elem_of_list_fmap. exists PExecL. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - left. apply elem_of_list_fmap. exists PExecR. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - right. apply elem_of_app. left.
    apply elem_of_list_fmap. exists sel. split; [reflexivity |].
    apply elem_of_choose. exact H.
  - left. apply elem_of_list_fmap. exists PPipe. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - right. apply elem_of_app. right.
    apply elem_of_list_fmap. exists sel. split; [reflexivity |].
    apply (elem_of_forkS_sels ws sel). exact H.
  - left. apply elem_of_list_fmap. exists PSilent. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
Qed.

(* THE MEMBERSHIP LAW, both ways: the list holds exactly the canonical
   codes of the alternatives the line admits. *)
Lemma elem_of_palt_cands l c :
  c ∈ palt_cands l <-> palt_ok l (palt_of c) /\ c = palt_code (palt_of c).
Proof using.
  split.
  - rewrite /palt_cands elem_of_app. intros [Hin | Hin].
    + apply elem_of_list_fmap in Hin as (a & -> & Ha).
      rewrite !palt_of_code. split; [| reflexivity].
      exact (proj1 (Forall_forall _ _) (palt_fix_cands_ok l) a Ha).
    + destruct l as [ws | ws]; [by apply elem_of_nil in Hin |].
      apply elem_of_app in Hin as [Hin | Hin].
      * apply elem_of_list_fmap in Hin as (sel & -> & Hsel).
        rewrite !palt_of_code. split; [| reflexivity].
        cbn [palt_ok]. by apply elem_of_choose.
      * apply elem_of_list_fmap in Hin as (sel & -> & Hsel).
        rewrite !palt_of_code. split; [| reflexivity].
        by apply (elem_of_forkS_sels ws sel).
  - intros [Hok Hc]. rewrite Hc. exact (palt_cands_alt l (palt_of c) Hok).
Qed.

Lemma palt_cands_canon l c :
  palt_ok l (palt_of c) -> palt_code (palt_of c) ∈ palt_cands l.
Proof using. exact (palt_cands_alt l (palt_of c)). Qed.

(* ====================================================================== *)
(*  3.  THE RESOLUTION LISTS, LINE BY LINE                                 *)
(* ====================================================================== *)

Fixpoint alts_cands_p (ls : list pline) : list (list nat) :=
  match ls with
  | [] => [[]]
  | l :: ls' =>
      (fun p => fst p :: snd p)
        <$> List.list_prod (palt_cands l) (alts_cands_p ls')
  end.

Lemma elem_of_alts_cands_p (ls : list pline) (cs : list nat) :
  cs ∈ alts_cands_p ls <-> Forall2 (fun l c => c ∈ palt_cands l) ls cs.
Proof using.
  revert cs. induction ls as [| l ls IH]; intros cs; cbn [alts_cands_p].
  - rewrite elem_of_list_singleton. split.
    + intros ->. constructor.
    + intro H. by apply Forall2_nil_inv_l in H.
  - rewrite elem_of_list_fmap. split.
    + intros ([c cs'] & -> & Hp). cbn [fst snd].
      apply elem_of_list_In, in_prod_iff in Hp as [Hc Hcs].
      apply elem_of_list_In in Hc. apply elem_of_list_In, IH in Hcs.
      by constructor.
    + intro H. apply Forall2_cons_inv_l in H as (c & cs' & Hc & Hcs & ->).
      exists (c, cs'). split; [reflexivity |].
      apply elem_of_list_In, in_prod_iff. split.
      * by apply elem_of_list_In.
      * by apply elem_of_list_In, IH.
Qed.

Lemma alts_cands_p_alts_ok (I : list (bv 8)) (cs : list nat) :
  cs ∈ alts_cands_p (plines_of I) -> alts_ok_p I cs.
Proof using.
  rewrite elem_of_alts_cands_p /alts_ok_p. intro H.
  eapply Forall2_impl; [exact H |]. intros l c Hc.
  exact (proj1 (proj1 (elem_of_palt_cands l c) Hc)).
Qed.

(* ====================================================================== *)
(*  4.  THE CANONICAL RESOLUTION                                           *)
(* ====================================================================== *)

(* EVERY consumer of [cs] reads it through [palt_at], so replacing each
   entry by the canonical code of its own decoding moves nothing.  (The
   route "[palt_ok l (palt_of c)] forces [c = palt_code (palt_of c)]" is
   NOT available: [palt_of] accepts codes that are not [palt_code]'s
   values -- e.g. every [n] with [n mod 16 = 11] decodes to a [PBoth],
   while [palt_code (PBoth sel)] is [11 + 16 * bnum sel] and [bnum] is
   not onto.) *)
Definition pcode_canon (c : nat) : nat := palt_code (palt_of c).

Definition cs_canon_p (cs : list nat) : list nat := pcode_canon <$> cs.

Lemma pcode_canon_0 : pcode_canon 0%nat = 0%nat.
Proof using.
  rewrite /pcode_canon (palt_of_lt4 0%nat ltac:(lia)).
  exact (palt_code_echo_lt4 0%nat ltac:(lia)).
Qed.

Lemma cs_canon_p_at cs i : palt_at (cs_canon_p cs) i = palt_at cs i.
Proof using.
  rewrite /palt_at /cs_canon_p (pdd_lookup_total_fmap _ cs i pcode_canon_0).
  rewrite /pcode_canon. by rewrite palt_of_code.
Qed.

Lemma pro_idx_p_canon cs i : pro_idx_p (cs_canon_p cs) i = pro_idx_p cs i.
Proof using.
  induction i as [| i IH]; [reflexivity |].
  by rewrite !pro_idx_p_S IH cs_canon_p_at.
Qed.

Lemma alt_cont_p_canon ps cs bs i :
  alt_cont_p ps (cs_canon_p cs) bs i = alt_cont_p ps cs bs i.
Proof using.
  by rewrite /alt_cont_p cs_canon_p_at pro_idx_p_canon.
Qed.

Lemma alt_seq_p_canon ps cs bs q :
  alt_seq_p ps (cs_canon_p cs) bs q = alt_seq_p ps cs bs q.
Proof using.
  induction q as [| q IH]; [reflexivity |].
  by rewrite !alt_seq_p_S IH /alt_blk_p alt_cont_p_canon.
Qed.

Lemma sessp_canon ps cs I : sessp ps (cs_canon_p cs) I = sessp ps cs I.
Proof using. by rewrite /sessp alt_seq_p_canon. Qed.

Lemma alts_ok_p_cs_canon (I : list (bv 8)) (cs : list nat) :
  alts_ok_p I cs -> cs_canon_p cs ∈ alts_cands_p (plines_of I).
Proof using.
  rewrite /alts_ok_p elem_of_alts_cands_p /cs_canon_p. intro H.
  apply Forall2_fmap_r. eapply Forall2_impl; [exact H |].
  intros l c Hc. exact (palt_cands_canon l c Hc).
Qed.

(* D4 reads [cs] only through [palt_at], so the canonical map moves it
   no more than it moves anything else. *)
Lemma d4_p_canon (cs : list nat) (I : list (bv 8)) :
  d4_p cs I -> d4_p (cs_canon_p cs) I.
Proof using.
  rewrite /d4_p. intro H. eapply Forall_impl; [exact H |].
  intros i Hi. by rewrite cs_canon_p_at.
Qed.

Lemma disc_pt_all_p_canon ps cs seg :
  disc_pt_all_p ps cs seg -> disc_pt_all_p ps (cs_canon_p cs) seg.
Proof using.
  rewrite /disc_pt_all_p. intro H. eapply Forall_impl; [exact H |].
  intros p [H1 H2]. split.
  - by rewrite /pro_ok_p pro_idx_p_canon.
  - by rewrite /disc_pt_p sessp_canon.
Qed.

(* ====================================================================== *)
(*  5.  THE PROLOGUE BOUND, AT [pro_idx_p]                                 *)
(* ====================================================================== *)

(* EVERY ROUND THE TRANSCRIPT ENTERS IS ON THE WIRE, so the prologue
   search is bounded by the segment.  [EchoDisc.alt_seq_pro_len]'s
   statement at [palt_panic]; the panic alternative is [PEcho 3] at BOTH
   line shapes ([PipeDisc.palt_ok_pipe_panic]), which is why this is one
   case and not two. *)
Lemma alt_seq_p_pro_len ps cs bs q r :
  (r <= pro_idx_p cs q)%nat ->
  (length (pro_of (pro_from r ps))
   <= length (pro_of ps) + length (alt_seq_p ps cs bs q))%nat.
Proof using.
  revert r. induction q as [| q IH]; intros r Hr.
  - assert (r = 0%nat) by (cbn [pro_idx_p] in Hr; lia). subst r.
    cbn [pro_from]. lia.
  - rewrite alt_seq_p_S length_app.
    destruct (decide (r <= pro_idx_p cs q)%nat) as [Hle | Hgt].
    + pose proof (IH r Hle). lia.
    + assert (Hp : palt_panic (palt_at cs q) = true).
      { destruct (palt_panic (palt_at cs q)) eqn:E; [reflexivity |].
        exfalso. rewrite (pro_idx_p_Sn cs q E) in Hr. lia. }
      rewrite (pro_idx_p_Sp cs q Hp) in Hr.
      assert (Hre : r = S (pro_idx_p cs q)) by lia.
      rewrite /alt_blk_p /alt_cont_p Hp !length_app.
      cbn [length]. rewrite length_app Hre. lia.
Qed.

Lemma sessp_pro_len ps cs I r :
  (r <= pro_idx_p cs (nlines I))%nat ->
  (length (pro_of (pro_from r ps)) <= length (sessp ps cs I))%nat.
Proof using.
  intro Hr. rewrite sessp_length.
  pose proof (alt_seq_p_pro_len ps cs (bodies_of I) (nlines I) r Hr). lia.
Qed.

(* ====================================================================== *)
(*  6.  THE DECISION                                                       *)
(* ====================================================================== *)

(* [EchoDisc.disc_seg'_dec]'s search at the two enumerators: the
   resolutions off the lines ([alts_cands_p], through [cs_canon_p]) and
   the prologues off [pro_cands] (through [pro_canon], applied unchanged
   -- it never mentions [cs]).  NOTHING HERE IS MEANT TO RUN: the
   ledger cases on it. *)
Global Instance disc_seg_p'_dec seg : Decision (disc_seg_p' seg).
Proof using.
  destruct (decide (disc_seg_p seg)) as [Hd | Hd];
    [| right; by intros [? _]].
  destruct (decide (Exists (fun cs =>
      d4_p cs (ins seg) /\
      Exists (fun ps => disc_pt_all_p ps cs seg)
        (pro_cands (S (pro_idx_p cs (nlines_max (in_pres seg))))
                   (length seg)))
      (alts_cands_p (plines_of (ins seg))))) as [HE | HE].
  - left. apply Exists_exists in HE as (cs & Hcs & [Hd4 HP]).
    apply Exists_exists in HP as (ps & _ & Hall).
    eapply disc_seg_p'_intro;
      [exact Hd | by apply alts_cands_p_alts_ok | exact Hd4 | exact Hall].
  - right. intros [_ (ps & cs & Hao & Hd4 & Hall)]. apply HE.
    apply Exists_exists. exists (cs_canon_p cs).
    split; [by apply alts_ok_p_cs_canon |].
    split; [by apply d4_p_canon |].
    rewrite pro_idx_p_canon. apply Exists_exists.
    (* the deepest checked point bounds every round the transcript enters *)
    destruct (decide (in_pres seg = [])) as [Hz | Hz].
    { destruct (pro_cands_nonempty
                  (S (pro_idx_p cs (nlines_max (in_pres seg)))) (length seg))
        as [g Hg].
      exists g. split; [exact Hg |]. rewrite /disc_pt_all_p Hz. constructor. }
    destruct (nlines_max_mem (in_pres seg) Hz) as (pl & Hplin & Hpleq).
    destruct (Hall pl Hplin) as [[HFps Hltl] Hptl].
    assert (Hplp : pl `prefix_of` seg)
      by exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) pl Hplin).
    destruct (pro_canon (S (pro_idx_p cs (nlines_max (in_pres seg))))
                (length seg) ps HFps) as (ps0 & Hin0 & Hrd0 & Hag0).
    { intros r Hr. rewrite -Hpleq in Hr. split; [lia |].
      etrans; [apply (sessp_pro_len ps cs (done_of (ins pl)) r);
               rewrite nlines_done; lia |].
      etrans; [apply prefix_length, Hptl |].
      etrans; [apply obs_wire_length |].
      exact (prefix_length _ _ Hplp). }
    exists ps0. split; [exact Hin0 |].
    apply disc_pt_all_p_canon.
    rewrite /disc_pt_all_p. apply Forall_forall. intros p Hp.
    destruct (Hall p Hp) as [[_ Hltp] Hptp].
    assert (Hidxle : (pro_idx_p cs (nlines (ins p))
                      <= pro_idx_p cs (nlines_max (in_pres seg)))%nat)
      by (apply pro_idx_p_mono, nlines_max_ge, Hp).
    assert (Hsame : sessp ps0 cs (done_of (ins p))
                    = sessp ps cs (done_of (ins p))).
    { apply sessp_ps_ext. intros r Hr. rewrite nlines_done in Hr.
      apply Hag0. lia. }
    split.
    + rewrite /pro_ok_p. split; [by eapply pro_cands_Forall | lia].
    + by rewrite /disc_pt_p Hsame.
Defined.

(* THE DELIVERABLE.  The pipeline discipline is decidable, so the
   pipeline ledger's taint counter reads [decide (disc_p h)] and lane
   PIPE-STAGE's [AppPipe.v] takes no [Decision] hypothesis. *)
(* OPAQUE ON PURPOSE, as [EchoDisc.disc_dec] and [FileDiscDec.disc_f_dec]
   are: the ledger's counter is [if decide (disc_p h) then 0 else 1] and
   every proof that touches it rewrites with a closure law.  A transparent
   instance would let ssreflect's [rewrite /pipe_led] iota-reduce the
   counter at a literal history and those rewrites would stop matching
   (FILE-DEC's finding, worth not re-discovering). *)
Global Instance disc_p_dec h : Decision (disc_p h).
Proof using. rewrite /disc_p. apply _. Qed.

(* ====================================================================== *)
(*  7.  THE ASSUMPTION CHECK                                              *)
(*                                                                        *)
(*  Iris-free and axiom-free.  All four print exactly Closed under the     *)
(*  global context (checked 2026-09-18 on the lane's mirror):              *)
(*                                                                        *)
(*    Print Assumptions elem_of_choose.                                    *)
(*    Print Assumptions elem_of_palt_cands.                                *)
(*    Print Assumptions disc_seg_p'_dec.                                   *)
(*    Print Assumptions disc_p_dec.                                        *)
(* ====================================================================== *)
