(* ===================================================================== *)
(* GrepTree.v -- the user program [grep] as an INTERACTION TREE, in       *)
(* [ProgTree]'s vocabulary (design: claude-notes/design/program-specs.md;  *)
(* the program's own design is claude-notes/design/grep.md).              *)
(*                                                                        *)
(*   - [match_re] is the Kernighan-Pike matcher of user/grep.c ([^ . *    *)
(*     $]), one Rocq function per C function, read off the C: it is the   *)
(*     spec of which lines grep prints.                                   *)
(*   - [scan] is the inner loop of grep(): the complete lines of the      *)
(*     buffer, each printed if it matches (the first one not at all while *)
(*     grep is SKIPPING the rest of an over-long line), and the LEFTOVER  *)
(*     that the C memmove()s to the front.  strchr stops at a NUL, so a   *)
(*     NUL byte leaves the rest of the buffer unscanned, exactly as the C *)
(*     does.                                                              *)
(*   - [grep_tree] is the program: the reads at [1023 - m] (the room      *)
(*     left in [buf]), one [EWrite 1] per matching line, the reset of a   *)
(*     full buffer that holds no newline (the line is too long: grep      *)
(*     skips it up to its newline), the per-file open/close, the two      *)
(*     diagnostics a byte at a time (usage by fprintf on fd 2,            *)
(*     cannot-open by printf on fd 1).                                    *)
(*   - [grep_out] is the readable statement of what grep owes: the        *)
(*     COMPLETE lines of the input of at most 1022 bytes that match, each *)
(*     with its newline.  The conformance theorems                        *)
(*     ([grep_stdin_conforms], [grep_file_conforms], ...) say the tree    *)
(*     prints exactly that, at every chunking of the input, on the        *)
(*     admissible inputs [grep_ok]: no NUL byte (demo_grep_nul).  The     *)
(*     room left in [buf] is never zero, so grep never issues a           *)
(*     zero-count read: [grep_tree_safe].                                 *)
(*                                                                        *)
(* Nothing imports this file yet: it is stated so that an application can *)
(* pick it up, and it sits above [ProgTree] only.                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list gmap bitvector.definitions.
Require Import StringBytes LineWords ProgTree.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE MATCHER (user/grep.c, after Kernighan & Pike)                  *)
(*                                                                        *)
(*  Patterns come from argv and lines from [scan], so neither contains a  *)
(*  NUL: the C's [re[k] == '\0'] and [*text == '\0'] are the ends of the   *)
(*  lists.  RISC-V's [char] is unsigned, so [*text++ == c] compares bytes. *)
(* ===================================================================== *)

Definition ch (n : Z) : bv 8 := Z_to_bv 8 n.
Definition c_nul    : bv 8 := ch 0.
Definition c_dollar : bv 8 := ch 36.    (* '$' *)
Definition c_star   : bv 8 := ch 42.    (* '*' *)
Definition c_dot    : bv 8 := ch 46.    (* '.' *)
Definition c_caret  : bv 8 := ch 94.    (* '^' *)

Definition bdec (a b : bv 8) : bool := bool_decide (a = b).

(*   int matchhere(char *re, char *text) {
       if (re[0] == '\0') return 1;
       if (re[1] == '*') return matchstar(re[0], re + 2, text);
       if (re[0] == '$' && re[1] == '\0') return *text == '\0';
       if ( *text != '\0' && (re[0] == '.' || re[0] == *text))
         return matchhere(re + 1, text + 1);
       return 0; }
     int matchstar(int c, char *re, char *text) {
       do { if (matchhere(re, text)) return 1;
       } while ( *text != '\0' && ( *text++ == c || c == '.'));
       return 0; }
   [matchstar] is the inner [fix]: its [re] is a subterm of matchhere's. *)
Fixpoint matchhere (re text : bytes) {struct re} : bool :=
  match re with
  | [] => true
  | c :: r =>
      let lit := match text with
                 | t :: ts => if bdec c c_dot || bdec c t then matchhere r ts else false
                 | [] => false
                 end in
      match r with
      | s :: r' =>
          if bdec s c_star then
            (fix matchstar (tx : bytes) : bool :=
               matchhere r' tx
               || match tx with
                  | t :: ts => (bdec t c || bdec c c_dot) && matchstar ts
                  | [] => false
                  end) text
          else lit
      | [] => if bdec c c_dollar then match text with [] => true | _ => false end else lit
      end
  end.

(* the [matchstar] of a [c*] prefix, as its own name for the proofs *)
Fixpoint matchstar (c : bv 8) (re text : bytes) : bool :=
  matchhere re text
  || match text with
     | t :: ts => (bdec t c || bdec c c_dot) && matchstar c re ts
     | [] => false
     end.

Lemma matchhere_star (c : bv 8) (re text : bytes) :
  matchhere (c :: c_star :: re) text = matchstar c re text.
Proof.
  simpl. unfold bdec at 1. rewrite bool_decide_true by reflexivity.
  induction text as [| t ts IH]; simpl; [reflexivity |]. rewrite IH. reflexivity.
Qed.

(*   int match(char *re, char *text) {
       if (re[0] == '^') return matchhere(re + 1, text);
       do { if (matchhere(re, text)) return 1; } while ( *text++ != '\0');
       return 0; }                                                        *)
Fixpoint match_any (re text : bytes) : bool :=
  matchhere re text || match text with _ :: ts => match_any re ts | [] => false end.

Definition match_re (re text : bytes) : bool :=
  match re with
  | c :: r => if bdec c c_caret then matchhere r text else match_any re text
  | [] => match_any re text
  end.

(* ===================================================================== *)
(*  2.  THE BUFFER SCAN: the inner loop of grep()                         *)
(*                                                                        *)
(*      p = buf;                                                          *)
(*      while ((q = strchr(p, '\n')) != 0) {                              *)
(*        *q = 0;                                                         *)
(*        if (!skip && match(pattern, p)) {                               *)
(*          *q = '\n'; write(1, p, q + 1 - p); }                          *)
(*        p = q + 1;                                                      *)
(*        skip = 0; }                                                     *)
(*                                                                        *)
(*  [scan pat skip cur s]: [cur] is the line begun so far (from [p]), [s]  *)
(*  the rest of the buffer up to its terminating NUL ([buf[m] = 0]),       *)
(*  [skip] whether the line begun is the tail of an over-long one.         *)
(*  Answers the lines written, in order, the leftover [buf[p..m)], and     *)
(*  [skip] after the scan (cleared by the first newline).                  *)
(* ===================================================================== *)

Fixpoint scan (pat : bytes) (skip : bool) (cur s : bytes) : list bytes * bytes * bool :=
  match s with
  | [] => ([], cur, skip)
  | b :: r =>
      if bdec b wl_nl then
        let res := scan pat false [] r in
        ((if skip then [] else if match_re pat cur then [cur ++ [wl_nl]] else [])
           ++ res.1.1, res.1.2, res.2)
      else if bdec b c_nul then ([], cur ++ s, skip)     (* strchr stops at the NUL *)
      else scan pat skip (cur ++ [b]) r
  end.

(* ===================================================================== *)
(*  3.  THE PROGRAM                                                       *)
(* ===================================================================== *)

(* char buf[1024]: a read asks for the room left, [sizeof(buf) - m - 1] *)
Definition grep_bufsz : nat := 1024.
Definition grep_room (left : bytes) : nat := (grep_bufsz - 1 - length left)%nat.

Definition grep_usage : bytes := sb "usage: grep pattern [file ...]" ++ [wl_nl].
Definition grep_dg_open (p : bytes) : bytes := sb "grep: cannot open " ++ p ++ [wl_nl].

(* grep(pattern, fd), from a state of the loop: [skip] the flag, [outs]
   the lines of the current buffer still to be written, [left] the
   leftover.  Written with the constructors (ProgTree SS3): the loop's
   back edge is the read's continuation.  The return of [write] is
   ignored; a read answering -1 or 0 ends the loop.  After the scan:

       if (m > 0) { m -= p - buf; memmove(buf, p, m);
                    if (m == sizeof(buf) - 1) { m = 0; skip = 1; } }

   The test is spelled [1023 <= m] rather than [m == 1023]: the two agree
   at every answer the kernel can give (a read delivers at most the count,
   so [m] never exceeds 1023), and the [<=] keeps the room positive at
   EVERY answer, which is what [grep_tree_safe] states. *)
CoFixpoint grep_go (pat : bytes) (fd : Z) (skip : bool) (outs : list bytes)
    (left : bytes) (rest : proc) : proc :=
  match outs with
  | o :: os => Vis (EWrite 1 o) (fun _ => grep_go pat fd skip os left rest)
  | [] =>
      Vis (ERead fd (grep_room left)) (fun a =>
        match a with
        | RdBytes (b :: bs) =>
            let sc := scan pat skip [] (left ++ b :: bs) in
            if decide (grep_bufsz - 1 <= length sc.1.2)%nat
            then grep_go pat fd true sc.1.1 [] rest
            else grep_go pat fd sc.2 sc.1.1 sc.1.2 rest
        | _ => rest
        end)
  end.

(*   main:  if (argc <= 1) { fprintf(2, usage); exit(1); }
            pattern = argv[1];
            if (argc <= 2) { grep(pattern, 0); exit(0); }
            for (i = 2; i < argc; i++) {
              if ((fd = open(argv[i], O_RDONLY)) < 0) {
                printf(grep: cannot open %s, argv[i]); exit(1); }
              grep(pattern, fd); close(fd); }
            exit(0);                                                      *)
Fixpoint grep_files (pat : bytes) (paths : list bytes) (rest : proc) : proc :=
  match paths with
  | [] => rest
  | p :: r =>
      Vis (EOpen p 0) (fun fd =>
        if decide (fd < 0) then write_bytes 1 (grep_dg_open p) (exit_ 1)
        else grep_go pat fd false [] [] (Vis (EClose fd) (fun _ => grep_files pat r rest)))
  end.

Definition grep_tree (argv : list bytes) : proc :=
  match drop 1 argv with
  | [] => write_bytes 2 grep_usage (exit_ 1)
  | [pat] => grep_go pat 0 false [] [] (exit_ 0)
  | pat :: paths => grep_files pat paths (exit_ 0)
  end.

Lemma grep_tree_tail (a b : list bytes) :
  drop 1 a = drop 1 b -> grep_tree a = grep_tree b.
Proof. intros H. unfold grep_tree. rewrite H. reflexivity. Qed.

Lemma grep_go_unfold (pat : bytes) (fd : Z) (skip : bool) (outs : list bytes)
    (left : bytes) (rest : proc) :
  grep_go pat fd skip outs left rest
  = match outs with
    | o :: os => Vis (EWrite 1 o) (fun _ => grep_go pat fd skip os left rest)
    | [] =>
        Vis (ERead fd (grep_room left)) (fun a =>
          match a with
          | RdBytes (b :: bs) =>
              let sc := scan pat skip [] (left ++ b :: bs) in
              if decide (grep_bufsz - 1 <= length sc.1.2)%nat
              then grep_go pat fd true sc.1.1 [] rest
              else grep_go pat fd sc.2 sc.1.1 sc.1.2 rest
          | _ => rest
          end)
    end.
Proof. etransitivity; [apply force_eq |]. destruct outs; reflexivity. Qed.

(* ===================================================================== *)
(*  4.  WHAT GREP OWES                                                    *)
(* ===================================================================== *)

(* the COMPLETE lines of an input (the unterminated tail is not one) *)
Fixpoint lines_acc (cur S : bytes) : list bytes :=
  match S with
  | [] => []
  | b :: r => if bdec b wl_nl then cur :: lines_acc [] r else lines_acc (cur ++ [b]) r
  end.
Definition lines (S : bytes) : list bytes := lines_acc [] S.

(* the longest line grep examines: 1022 bytes and its newline fill [buf] *)
Definition grep_maxline : nat := 1022.

Definition grep_line_ok (pat l : bytes) : bool :=
  bool_decide (length l <= grep_maxline)%nat && match_re pat l.

Definition grep_out (pat S : bytes) : bytes :=
  concat (map (fun l => l ++ [wl_nl]) (filter (fun l => grep_line_ok pat l = true) (lines S))).

(* the admissible inputs: no NUL byte *)
Definition grep_ok (S : bytes) : Prop := Forall (fun b => b <> c_nul) S.

(* ===================================================================== *)
(*  5.  DEMOS                                                             *)
(* ===================================================================== *)

Definition argv_grep (ws : list string) : list bytes := sb "grep" :: map sb ws.
Definition nl : bytes := [wl_nl].
Definition cons_in (s : bytes) : world := MkW s [] [] [].
Definition grep_demo_in : bytes := sb "foo" ++ nl ++ sb "bar" ++ nl ++ sb "boo" ++ nl.

(* the matcher at each operator *)
Example demo_match :
  map (fun '(re, t) => match_re (sb re) (sb t))
    [("o", "foo"); ("^f", "foo"); ("^o", "foo"); ("o$", "foo"); ("f$", "foo");
     ("f.o", "foo"); ("fo*", "f"); ("^fo*$", "fooo"); ("^fo*$", "foox");
     ("a*b", "aab"); (".*", ""); ("", "x"); ("x*", "yyy"); ("$", "abc")]
  = [true; true; false; true; false;
     true; true; true; false;
     true; true; true; true; true].
Proof. vm_compute. reflexivity. Qed.

(* grep o, the console as input: the two lines with an o *)
Example demo_grep_stdin :
  (line_plain (cons_in grep_demo_in) (grep_tree (argv_grep ["o"]))).1.(w_cons)
  = sb "foo" ++ nl ++ sb "boo" ++ nl.
Proof. vm_compute. reflexivity. Qed.

(* ...and it is [grep_out] *)
Example demo_grep_is_grep_out :
  (line_plain (cons_in grep_demo_in) (grep_tree (argv_grep ["^b"]))).1.(w_cons)
  = grep_out (sb "^b") grep_demo_in.
Proof. vm_compute. reflexivity. Qed.

(* the unterminated tail is never printed, even when it matches *)
Example demo_grep_tail :
  (line_plain (cons_in (sb "foo" ++ nl ++ sb "foo")) (grep_tree (argv_grep ["foo"]))).1.(w_cons)
  = sb "foo" ++ nl.
Proof. vm_compute. reflexivity. Qed.

(* a file, after `echo foo bar > f`; a missing file prints on FD 1 *)
Definition w_file : world := file_set (cons_in []) (sb "f") grep_demo_in.
Example demo_grep_file :
  (line_plain w_file (grep_tree (argv_grep ["b.o"; "f"]))).1.(w_cons) = sb "boo" ++ nl.
Proof. vm_compute. reflexivity. Qed.
Example demo_grep_absent :
  let '(w, o) := line_plain w_file (grep_tree (argv_grep ["o"; "f"; "g"])) in
  w_cons w = sb "foo" ++ nl ++ sb "boo" ++ nl ++ sb "grep: cannot open g" ++ nl
  /\ o = Exited 1.
Proof. vm_compute. split; reflexivity. Qed.
Example demo_grep_usage :
  let '(w, o) := line_plain w0 (grep_tree (argv_grep [])) in
  w_cons w = grep_usage /\ o = Exited 1.
Proof. vm_compute. split; reflexivity. Qed.

(* echo foo | grep o, and cat f | grep ^b *)
Example demo_grep_pipe :
  (line_pipe w0 (echo_tree (argv_echo ["foo"])) (grep_tree (argv_grep ["o"]))).1.(w_cons)
  = sb "foo" ++ nl.
Proof. vm_compute. reflexivity. Qed.
Example demo_cat_grep :
  (line_pipe w_file (cat_tree (argv_cat ["f"])) (grep_tree (argv_grep ["^b"]))).1.(w_cons)
  = sb "bar" ++ nl ++ sb "boo" ++ nl.
Proof. vm_compute. reflexivity. Qed.

(* an input longer than [buf]: the first read stops mid-line, the leftover
   is carried to the front, and every line still comes out *)
Definition many_lines : bytes := concat (replicate 400 (sb "ab" ++ nl)).
Example demo_grep_chunked :
  (line_plain (cons_in many_lines) (grep_tree (argv_grep ["b"]))).1.(w_cons) = many_lines.
Proof. vm_compute. reflexivity. Qed.

(* A LINE TOO LONG FOR [buf] IS SKIPPED, and the search goes on after it:
   1022 bytes is the longest line grep examines, 1023 is skipped, and a
   line several buffers long is skipped across every reset *)
Definition long_in (k : nat) : bytes := replicate k (ch 97) ++ nl ++ sb "ab" ++ nl.
Example demo_grep_long_line :
  map (fun k => (line_plain (cons_in (long_in k)) (grep_tree (argv_grep ["a"]))).1.(w_cons))
      [1022; 1023; 3000]%nat
  = [long_in 1022; sb "ab" ++ nl; sb "ab" ++ nl].
Proof. vm_compute. reflexivity. Qed.
Example demo_grep_long_is_grep_out :
  (line_plain (cons_in (long_in 1100)) (grep_tree (argv_grep ["a"]))).1.(w_cons)
  = grep_out (sb "a") (long_in 1100).
Proof. vm_compute. reflexivity. Qed.

(* A NUL BYTE STILL STOPS THE SCAN: strchr never gets past it, so the
   lines after it are lost unless the buffer later fills.  Hence [grep_ok]. *)
Example demo_grep_nul :
  (line_plain (cons_in (sb "a" ++ [c_nul] ++ sb "b" ++ nl ++ sb "ab" ++ nl))
     (grep_tree (argv_grep ["a"]))).1.(w_cons) = [].
Proof. vm_compute. reflexivity. Qed.

(* A NEGATIVE ONE: the pattern decides *)
Example demo_grep_negative :
  (line_plain (cons_in grep_demo_in) (grep_tree (argv_grep ["f"]))).1.(w_cons)
  <> (line_plain (cons_in grep_demo_in) (grep_tree (argv_grep ["r"]))).1.(w_cons).
Proof. vm_compute. discriminate. Qed.

(* ===================================================================== *)
(*  6.  THE SCAN, PURELY                                                  *)
(* ===================================================================== *)

(* the output owed from a line begun at [cur] *)
Fixpoint gout (pat cur S : bytes) : bytes :=
  match S with
  | [] => []
  | b :: r =>
      if bdec b wl_nl then (if grep_line_ok pat cur then cur ++ [wl_nl] else []) ++ gout pat [] r
      else gout pat (cur ++ [b]) r
  end.

(* the input after the first newline (none: nothing) *)
Fixpoint gdrop (S : bytes) : bytes :=
  match S with
  | [] => []
  | b :: r => if bdec b wl_nl then r else gdrop r
  end.

(* ...and while skipping, the line begun is not owed at all *)
Definition gout_s (pat : bytes) (skip : bool) (cur S : bytes) : bytes :=
  if skip then gout pat [] (gdrop S) else gout pat cur S.

Lemma gout_lines (pat cur S : bytes) :
  gout pat cur S
  = concat (map (fun l => l ++ [wl_nl]) (filter (fun l => grep_line_ok pat l = true) (lines_acc cur S))).
Proof.
  revert cur. induction S as [| b r IH]; intros cur; [reflexivity |].
  simpl. destruct (bdec b wl_nl); [| apply IH].
  rewrite filter_cons. destruct (grep_line_ok pat cur) eqn:Hm; simpl; rewrite IH; reflexivity.
Qed.

Lemma grep_out_gout (pat S : bytes) : grep_out pat S = gout_s pat false [] S.
Proof. unfold grep_out, lines, gout_s. by rewrite gout_lines. Qed.

(* a byte the scan passes over: neither a newline nor a NUL *)
Definition clean (b : bv 8) : Prop := b <> wl_nl /\ b <> c_nul.

Lemma bdec_true (a b : bv 8) : a = b -> bdec a b = true.
Proof. intros ->. unfold bdec. by rewrite bool_decide_true. Qed.
Lemma bdec_false (a b : bv 8) : a <> b -> bdec a b = false.
Proof. intros H. unfold bdec. by rewrite bool_decide_false. Qed.
Lemma bdec_spec (a b : bv 8) : bdec a b = true <-> a = b.
Proof. unfold bdec. apply bool_decide_eq_true. Qed.

(* the scan over a clean prefix only extends the line begun *)
Lemma scan_clean_app (pat : bytes) (skip : bool) (cur x y : bytes) :
  Forall clean x -> scan pat skip cur (x ++ y) = scan pat skip (cur ++ x) y.
Proof.
  revert cur. induction x as [| b x IH]; intros cur Hx.
  - by rewrite app_nil_r.
  - apply Forall_cons_1 in Hx as [[Hn Hz] Hx]. simpl.
    rewrite (bdec_false _ _ Hn), (bdec_false _ _ Hz), IH by exact Hx.
    by rewrite <- app_assoc.
Qed.

(* what the scan writes, followed by what is owed from its leftover, is what
   was owed from the line begun: the chunking does not show.  The buffer
   holds at most 1023 bytes, so every line the scan finds is one grep
   examines. *)
Lemma scan_gout (pat : bytes) (skip : bool) (cur S T : bytes) :
  Forall (fun b => b <> c_nul) S -> (length cur + length S <= 1023)%nat ->
  concat (scan pat skip cur S).1.1 ++ gout_s pat (scan pat skip cur S).2 (scan pat skip cur S).1.2 T
  = gout_s pat skip cur (S ++ T).
Proof.
  revert cur skip. induction S as [| b r IH]; intros cur skip HS Hlen; [reflexivity |].
  apply Forall_cons_1 in HS as [Hz HS]. simpl in Hlen |- *.
  destruct (bdec b wl_nl) eqn:Hn.
  - cbn [fst snd]. rewrite concat_app, <- app_assoc, IH by (exact HS || simpl; lia).
    unfold gout_s at 2. destruct skip; simpl.
    + rewrite Hn. reflexivity.
    + rewrite Hn. unfold grep_line_ok, grep_maxline.
      rewrite bool_decide_true by lia.
      destruct (match_re pat cur); simpl; [by rewrite app_nil_r | reflexivity].
  - rewrite (bdec_false _ _ Hz). rewrite IH by (exact HS || rewrite length_app; simpl; lia).
    unfold gout_s. destruct skip; simpl; rewrite Hn; reflexivity.
Qed.

(* a line already 1023 bytes long is owed nothing, whatever follows *)
Lemma gout_long (pat cur T : bytes) :
  (1023 <= length cur)%nat -> gout pat cur T = gout pat [] (gdrop T).
Proof.
  revert cur. induction T as [| b r IH]; intros cur Hl; [reflexivity |].
  simpl. destruct (bdec b wl_nl).
  - unfold grep_line_ok, grep_maxline. rewrite bool_decide_false by lia. reflexivity.
  - apply IH. rewrite length_app. lia.
Qed.

Lemma gout_s_reset (pat : bytes) (skip : bool) (cur T : bytes) :
  (1023 <= length cur)%nat -> gout_s pat skip cur T = gout_s pat true [] T.
Proof. intros Hl. unfold gout_s. destruct skip; [reflexivity | by apply gout_long]. Qed.

Lemma scan_leftover_clean (pat : bytes) (skip : bool) (cur S : bytes) :
  Forall clean cur -> Forall (fun b => b <> c_nul) S -> Forall clean (scan pat skip cur S).1.2.
Proof.
  revert cur skip. induction S as [| b r IH]; intros cur skip Hc HS; [exact Hc |].
  apply Forall_cons_1 in HS as [Hz HS]. simpl.
  destruct (bdec b wl_nl) eqn:Hn.
  - apply IH; [constructor | exact HS].
  - rewrite (bdec_false _ _ Hz). apply IH; [| exact HS].
    apply Forall_app; split; [exact Hc |]. constructor; [| constructor].
    split; [| exact Hz]. intros Heq. rewrite (bdec_true _ _ Heq) in Hn. discriminate.
Qed.

Lemma scan_outs_ne (pat : bytes) (skip : bool) (cur S : bytes) :
  Forall (fun b => b <> c_nul) S -> Forall (fun o => o <> []) (scan pat skip cur S).1.1.
Proof.
  revert cur skip. induction S as [| b r IH]; intros cur skip HS; [constructor |].
  apply Forall_cons_1 in HS as [Hz HS]. simpl.
  destruct (bdec b wl_nl).
  - simpl. apply Forall_app. split; [| apply IH, HS].
    destruct skip; [constructor |].
    destruct (match_re pat cur); constructor; [| constructor].
    intros H. apply (f_equal (@length _)) in H. rewrite length_app in H. simpl in H. lia.
  - rewrite (bdec_false _ _ Hz). apply IH. exact HS.
Qed.

Lemma gout_s_nil (pat : bytes) (skip : bool) (cur : bytes) : gout_s pat skip cur [] = [].
Proof. by destruct skip. Qed.

(* ===================================================================== *)
(*  7.  CONFORMANCE                                                       *)
(*                                                                        *)
(*  grep in [ProgTree.cat_env]'s environment -- the console (device 0) on  *)
(*  descriptors 1 and 2, the input device [din] on [fdin] -- owes exactly  *)
(*  [grep_out] of its input, at every chunking.  The loop's invariant: the *)
(*  lines of the current buffer still to write, then what is owed from the *)
(*  leftover at the flag, is an alternative the console owes; the leftover *)
(*  is under 1023 bytes, so the room is positive.                         *)
(* ===================================================================== *)

Lemma grep_go_conforms (pat : bytes) (fdin : Z) (din : nat) files paths (rest : proc) :
  din <> 0%nat -> fdin <> 1 -> fdin <> 2 ->
  (forall alts', [] ∈ alts' -> conforms (cat_env fdin din [] alts' files paths) rest) ->
  forall skip outs left S alts,
    Forall (fun o => o <> []) outs -> Forall clean left -> (length left < 1023)%nat ->
    grep_ok S ->
    concat outs ++ gout_s pat skip left S ∈ alts ->
    conforms (cat_env fdin din S alts files paths) (grep_go pat fdin skip outs left rest).
Proof.
  intros Hd Hf1 Hf2 Hrest. cofix CIH. intros skip outs left S alts Hne Hcl Hlen Hok Hin.
  rewrite grep_go_unfold. destruct outs as [| o os].
  - (* the read, at the room left: at least one byte *)
    eapply cf_read with (d := din) (S := S).
    { unfold grep_room, grep_bufsz. lia. }
    { cbv [cat_env pe_fd]. rewrite lookup_insert_ne; [| lia].
      rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
    { cbv [cat_env pe_fd pe_dev]. rewrite decide_False; [| exact Hd]. first [ by rewrite decide_True | done ]. }
    intros c S' (HS & Hclen & Hnil). rewrite cat_env_in; [| exact Hd].
    destruct c as [| b c'].
    + (* end of file: nothing more is owed *)
      assert (S = []) as -> by exact (Hnil eq_refl).
      simpl in HS. destruct S'; [| discriminate HS].
      apply Hrest. simpl in Hin. rewrite gout_s_nil in Hin. exact Hin.
    + subst S. cbv zeta.
      unfold grep_ok in Hok. apply Forall_app in Hok as [Hnul Hok'].
      assert (Hbuf : (length left + length (b :: c') <= 1023)%nat)
        by (unfold grep_room, grep_bufsz in Hclen; lia).
      rewrite scan_clean_app by exact Hcl. simpl app.
      pose proof (scan_gout pat skip left (b :: c') S' Hnul Hbuf) as Hg.
      destruct (decide (grep_bufsz - 1 <= length (scan pat skip left (b :: c')).1.2)%nat) as [Hfull | Hroom].
      * (* the buffer is full and holds no newline: skip the line *)
        apply CIH; [apply scan_outs_ne, Hnul | constructor | simpl; lia | exact Hok' |].
        rewrite <- (gout_s_reset pat (scan pat skip left (b :: c')).2
                      (scan pat skip left (b :: c')).1.2 S')
          by (unfold grep_bufsz in Hfull; lia).
        rewrite Hg. simpl in Hin. exact Hin.
      * apply CIH.
        -- apply scan_outs_ne. exact Hnul.
        -- apply scan_leftover_clean; [exact Hcl | exact Hnul].
        -- unfold grep_bufsz in Hroom. lia.
        -- exact Hok'.
        -- rewrite Hg. simpl in Hin. exact Hin.
  - (* a line: a nonempty chunk of the owed alternative *)
    apply Forall_cons_1 in Hne as [Hne Hne'].
    simpl in Hin.
    eapply cf_write with (d := 0%nat) (alts := alts) (a := o ++ concat os ++ gout_s pat skip left S).
    { exact Hne. }
    { cbv [cat_env pe_fd]. apply lookup_insert. }
    { cbv [cat_env pe_fd pe_dev]. by rewrite decide_True. }
    { rewrite <- app_assoc in Hin. exact Hin. }
    { by eexists. }
    rewrite drop_app_length, cat_env_out.
    apply CIH; [exact Hne' | exact Hcl | exact Hlen | exact Hok | by left].
Qed.

(* grep PAT with no file: the standard input, copied through the matcher *)
Theorem grep_stdin_conforms (pat S : bytes) files paths :
  grep_ok S ->
  conforms (cat_env 0 1 S [grep_out pat S] files paths) (grep_tree [sb "grep"; pat]).
Proof.
  intros Hok. unfold grep_tree. simpl drop.
  apply grep_go_conforms; [done | done | done | | constructor | constructor | simpl; lia | exact Hok |].
  - intros alts' Hin. apply cat_env_exit. exact Hin.
  - rewrite grep_out_gout. by left.
Qed.

(* grep PAT f: the matching lines of f, or (the kernel may refuse the open)
   the diagnostic, on descriptor 1 *)
Theorem grep_file_conforms (pat f content : bytes) files :
  files f = Some content -> grep_ok content ->
  conforms (cat_env0 [grep_out pat content; grep_dg_open f] files [f])
           (grep_tree [sb "grep"; pat; f]).
Proof.
  intros Hf Hok. unfold grep_tree. simpl drop. simpl grep_files.
  eapply cf_open_present; [by left | exact Hf | |].
  - intros fd d Hfd Hnone Hfr. rewrite cat_env0_open; [| exact Hnone | exact Hfr].
    rewrite decide_False; [| lia].
    assert (fd <> 1 /\ fd <> 2) as [Hf1 Hf2].
    { cbv [cat_env0 pe_fd] in Hnone. split; intros ->; simplify_map_eq. }
    assert (d <> 0%nat) as Hd0.
    { intros ->. apply (Hfr 1). cbv [cat_env0 pe_fd]. apply lookup_insert. }
    apply grep_go_conforms; [exact Hd0 | exact Hf1 | exact Hf2 | | constructor | constructor | simpl; lia | exact Hok |].
    + intros alts' Hin.
      eapply cf_close with (d := d).
      { cbv [cat_env pe_fd]. rewrite lookup_insert_ne; [| lia].
        rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
      { intros _. cbv [cat_env pe_dev]. repeat case_decide; exact I. }
      simpl. apply cf_exit. intros d'. unfold drained. cbv [env_unbind cat_env pe_dev].
      destruct (decide (d' = 0%nat)); [exact Hin |].
      destruct (decide (d' = d)); [exact I | by left].
    + rewrite <- grep_out_gout. by left.
  - cbv beta. rewrite decide_True; [| lia].
    eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := [grep_out pat content; grep_dg_open f]).
    { cbv [cat_env0 pe_fd]. apply lookup_insert. }
    { reflexivity. }
    { rewrite app_nil_r. by right; left. }
    intros alts' Hin. rewrite cat_env0_out. apply cat_env0_exit. exact Hin.
Qed.

Theorem grep_file_absent_conforms (pat f : bytes) files :
  files f = None ->
  conforms (cat_env0 [grep_dg_open f] files [f]) (grep_tree [sb "grep"; pat; f]).
Proof.
  intros Hf. unfold grep_tree. simpl drop. simpl grep_files.
  eapply cf_open_absent; [by left | unfold mode_create; vm_compute; intros H; exact (H eq_refl) | exact Hf |].
  cbv beta. rewrite decide_True; [| lia].
  eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := [grep_dg_open f]).
  { cbv [cat_env0 pe_fd]. apply lookup_insert. }
  { reflexivity. }
  { rewrite app_nil_r. by left. }
  intros alts' Hin. rewrite cat_env0_out. apply cat_env0_exit. exact Hin.
Qed.

(* grep with no pattern: the usage line on descriptor 2 *)
Theorem grep_usage_conforms files paths :
  conforms (cat_env0 [grep_usage] files paths) (grep_tree [sb "grep"]).
Proof.
  unfold grep_tree. simpl drop.
  eapply write_bytes_conforms with (d := 0%nat) (S' := []) (alts := [grep_usage]).
  { cbv [cat_env0 pe_fd]. rewrite lookup_insert_ne; [| lia]. apply lookup_singleton. }
  { reflexivity. }
  { rewrite app_nil_r. by left. }
  intros alts' Hin. rewrite cat_env0_out. apply cat_env0_exit. exact Hin.
Qed.

(* ===================================================================== *)
(*  8.  THE DESCRIPTOR DISCIPLINE UNDER ANY ANSWER                        *)
(*                                                                        *)
(*  Whatever the kernel answers, grep reads with a positive count (the     *)
(*  leftover is under 1023 bytes: a full buffer is reset) and closes only  *)
(*  the descriptor it opened.                                             *)
(* ===================================================================== *)

Lemma grep_go_safe (pat : bytes) (fd : Z) (rest : proc) (held : gset Z) :
  safe_fds held rest ->
  forall skip outs left, (length left < 1023)%nat ->
    safe_fds held (grep_go pat fd skip outs left rest).
Proof.
  intros Hrest. cofix CIH. intros skip outs left Hlen.
  rewrite grep_go_unfold. destruct outs as [| o os].
  - apply sf_read; [unfold grep_room, grep_bufsz; lia |].
    intros [| [| b bs]]; [exact Hrest | exact Hrest |]. cbv zeta.
    destruct (decide _) as [Hfull | Hroom].
    + apply CIH. simpl. lia.
    + apply CIH. unfold grep_bufsz in Hroom. lia.
  - apply sf_write. intros _. apply CIH. exact Hlen.
Qed.

Lemma grep_files_safe (pat : bytes) (paths : list bytes) (held : gset Z) :
  safe_fds held (grep_files pat paths (exit_ 0)).
Proof.
  revert held. induction paths as [| p r IH]; intros held; simpl; [apply sf_exit |].
  apply sf_open.
  - intros fd Hfd. rewrite decide_False; [| lia].
    apply grep_go_safe; [| simpl; lia].
    apply sf_close; [set_solver |]. intros _. apply IH.
  - rewrite decide_True; [| lia]. apply (write_bytes_safe 1 (grep_dg_open p) (exit_ 1)). apply sf_exit.
Qed.

Theorem grep_tree_safe (argv : list bytes) (held : gset Z) :
  safe_fds held (grep_tree argv).
Proof.
  unfold grep_tree. destruct (drop 1 argv) as [| pat [| p r]].
  - apply (write_bytes_safe 2 grep_usage (exit_ 1)). apply sf_exit.
  - apply grep_go_safe; [apply sf_exit | simpl; lia].
  - apply grep_files_safe.
Qed.
