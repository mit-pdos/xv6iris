(* EchoDisc.v -- THE ECHO APPLICATION'S CONSOLE DISCIPLINE AND OUTPUT CLAIM,
   as PURE COMBINATORICS over the observation trace.  No Iris, no ghosts: a
   [list mobs] goes in and a [Prop] comes out, so the statements here can be
   read -- and refuted -- without opening the logic.

   Design of record: claude-notes/projects/echo-any-line.md, "The design
   (owner's session, 2026-09-16)" for the line-per-round session model;
   claude-notes/projects/app-echo.md, "E5 -- THE OUTPUT SIDE" (O1-O3 as ruled
   by the owner; O5's allocation-failure alternatives; "TWO UARTS") and "E3 --
   THE INPUT LINE" (R4, the per-character ruling); the pre-mortem review
   review-echo-plan-2026-09-12.md, findings 7, 8 and 12.

   THE THEOREM IS ABOUT THE CONSOLE UART ONLY.  The board has two 16550s
   and the kernel drives both: the CONSOLE ([DevModel.Uart0]) carries the
   processes' output and [consoleintr]'s echo of what the user types, and
   nothing else -- [printk] and [panic] write the OTHER port
   ([DevModel.Uart1]), whose output is unconstrained and which this file
   never reads.  So the console wire is PURE SESSION OUTPUT: what a user
   sees is exactly what init, sh, echo and the echo-back produced, in the
   order the transmitter accepted it.  (Before the second port existed the
   kernel's ten boot messages were interleaved into the same wire, byte for
   byte, and the discipline had to wait for the last of them before it
   could read anything; all of that is gone.)

   WHY THE DISCIPLINE IS A RATE BOUND.  A discipline on the cycle's INPUT
   BYTES ALONE says nothing about WHEN a byte was typed.  Review finding 7 is
   that the theorem is FALSE at such a discipline: the console ring holds 128
   unconsumed bytes and [consoleintr] DROPS the next one silently, so an
   adversary who types a screenful before sh's first read breaks the
   correspondence between the stored sequence and the input sequence, and
   nothing downstream can repair it.  The rate bound is stated on the raw
   wire, and it is PER LINE:

     D1  a line's first byte only after the "$ " prompt has appeared.
     D3  the input PARSES as a sequence of admissible lines, plus a line
         the user has only started -- [disc_input] below.

   THE USER TYPES A WHOLE LINE AS A BURST.  Within a line nothing is asked:
   once the prompt is there, every byte of that line may arrive before any
   of its echoes.  Section 4 states, at every input position, that the
   expected transcript for the input's COMPLETE LINES ([LineWords.done_of])
   is already a prefix of the wire ([disc_pt]).  That transcript ends in
   exactly the "$ " D1 asks for at a line boundary (at the empty input it
   is init's banner and sh's first prompt), and mid-line it is the same
   transcript the line's first byte demanded, so the one condition is D1.

   WHAT BOUNDS THE RING is therefore not the wire but the CLAIM: at most
   one line is outstanding because the user waits for the previous line's
   block to end in "$ ", and [line_max] keeps a line under the ring's 128.
   The claim states that as a delivered-count clause and refutes
   [ConsLog.cons_drop_ok]'s full-ring arm from it
   ([EchoOutPure.drop_refuted]); the discipline itself does not pin the
   wire at an input point.

   EACH ROUND TYPES ITS OWN LINE.  The session is a function of the era's
   INPUT, not of its length: [sess ps cs I] reads [I] through the parser of
   [LineWords] section 7 -- the complete bodies [bodies_of I] and the
   partial line [rest_of I] -- so nothing here divides the wire by a fixed
   line length, and every round carries whatever words the user typed for
   it.  What makes that sound is that the parse of a prefix is a prefix of
   the parse, so the observer reads the rounds off the wire
   ([EchoOutPure.sess_prefix_det]).

   WHAT IS NOT HERE.  [Hphi] -- the theorem's obligation at [echo_phi] --
   is NOT proved by this file, nor by the lane that wrote it; see the note
   at [AppEcho.echo_phi].  This file is the STATEMENT. *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [obs_wire Uart0], [cycles_of], [trace_shape] *)
Require Import StringBytes.      (* [string_bytes] *)
Require Import LineWords.        (* the line as a list of WORDS *)
(* ssreflect's [rewrite] (the [/def] fold, the multi-rule form) is what this
   file's proofs are written in; a pure file does not get it from the
   proofmode the way its neighbours do, so it is imported by name. *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  BYTES FROM STRINGS                                                 *)
(* ====================================================================== *)

(* the kernel's own string->bytes reader, NUL-free.  Every literal below is
   transcribed from the source it comes from and from nothing else: a
   message that is wrong here makes the claim say something the machine
   does not do, and no build step would notice. *)
Definition sb (s : string) : list (bv 8) := string_bytes s.

Definition nlb : list (bv 8) := [Z_to_bv 8 10%Z].

(* ====================================================================== *)
(*  1.  THE LINE THE DISCIPLINE ADMITS, AND D3                             *)
(* ====================================================================== *)

(* THE CONSOLE LINE THE DISCIPLINE ADMITS is a WORD LINE ([LineWords]):
   words joined by single spaces and closed by the newline [gets] stops at
   and keeps.  These are the bytes the user types, and ALSO their echoes,
   because [consoleintr] echoes a stored byte unchanged and rewrites only
   '\r' (to '\n'); an admissible line ends in '\n' (byte 10), not '\r', so
   the echo is the IDENTITY on it.

   THE FOUR CONDITIONS are the whole of what the claim excludes, and each
   is owed by a named consumer: the words are words ([wl_wf], so sh's lexer
   finds them and no byte of the line is a control character); the command
   run IS /echo, because the theorem is about that program; there are fewer
   words than sh's MAXARGS; and the line fits [getcmd]'s buffer.  Nothing
   here excludes [echo fork] or [echo exec echo failed] -- see the note at
   [line_alts_of_prefix_bytes]. *)
Definition cmd_echo : list (bv 8) := sb "echo"%string.

(* sh's [getcmd] buffer ([UkSh.sh_nbuf]), which UkSh proves equal to this.
   The console ring's 128 follows: at most one line is ever outstanding. *)
Definition line_max : nat := 100.

Definition line_ok (ws : list (list (bv 8))) : Prop :=
  wl_wf ws
  /\ ws !! 0%nat = Some cmd_echo
  /\ (2 <= length ws)%nat
  /\ (length ws < 10)%nat
  /\ (length (wl_line ws) < line_max)%nat.

Global Instance line_ok_dec ws : Decision (line_ok ws).
Proof. rewrite /line_ok. apply _. Defined.

Lemma line_ok_wf ws : line_ok ws -> wl_wf ws.
Proof. by intros (H & _ & _ & _ & _). Qed.

Lemma line_ok_head ws : line_ok ws -> ws !! 0%nat = Some cmd_echo.
Proof. by intros (_ & H & _ & _ & _). Qed.

(* AT LEAST ONE ARGUMENT.  echo's loop runs from 1 to [argc], so at
   [argc = 1] it prints NOTHING -- while the line's own tail is the bare
   newline.  The claim's good alternative IS that tail
   ([line_alts_of]'s 0), so a line with no argument is a line this claim
   must not be about, and this is where it says so. *)
Lemma line_ok_ge2 ws : line_ok ws -> (2 <= length ws)%nat.
Proof. by intros (_ & _ & H & _ & _). Qed.

Lemma line_ok_lt10 ws : line_ok ws -> (length ws < 10)%nat.
Proof. by intros (_ & _ & _ & H & _). Qed.

Lemma line_ok_len ws : line_ok ws -> (length (wl_line ws) < line_max)%nat.
Proof. by intros (_ & _ & _ & _ & H). Qed.

Lemma line_ok_pos ws : line_ok ws -> (0 < length ws)%nat.
Proof.
  intro Hok. exact (lookup_lt_Some ws 0%nat cmd_echo (line_ok_head ws Hok)).
Qed.

(* the COMMAND NAME is four bytes and opens with 'e' -- the two readings
   the shell's own walk spends, and the only numbers any line supplies *)
Lemma line_ok_head_len ws : line_ok ws -> length (ws !!! 0%nat) = 4%nat.
Proof.
  intro Hok.
  rewrite (list_lookup_total_correct ws 0%nat cmd_echo (line_ok_head ws Hok)).
  by vm_compute.
Qed.

Lemma line_ok_head_byte0 ws :
  line_ok ws -> bv_unsigned (wl_line ws !!! 0%nat) = 101%Z.
Proof.
  intro Hok. pose proof (line_ok_head ws Hok) as Hh.
  assert (Hlt : (0 < length cmd_echo)%nat) by (vm_compute; lia).
  pose proof (wl_line_word ws 0%nat cmd_echo 0%nat Hh Hlt) as Hw.
  replace (wl_off 0%nat ws 0%nat + 0)%nat with 0%nat in Hw
    by (rewrite wl_off_0; lia).
  rewrite Hw. by vm_compute.
Qed.

(* a word of the line, read back through [!!] so that [LineWords]' lemmas
   -- every one of which is keyed on [ws !! i = Some w] -- apply *)
Lemma line_ok_at ws i :
  line_ok ws -> (i < length ws)%nat -> ws !! i = Some (ws !!! i).
Proof.
  intros _ Hi. destruct (lookup_lt_is_Some_2 ws i Hi) as [w Hw].
  by rewrite Hw list_lookup_total_alt Hw.
Qed.

(* A BODY IS A WELL-FORMED JOIN OF ITS OWN WORDS.  The parser is total, so
   what rejects a body is this equation (a double blank, a trailing blank)
   or [line_ok], never the parser. *)
Definition body_ok (l : list (bv 8)) : Prop :=
  wl_body (wl_words l) = l /\ line_ok (wl_words l).

Global Instance body_ok_dec l : Decision (body_ok l).
Proof. rewrite /body_ok. apply _. Defined.

Lemma body_ok_bytes l : body_ok l -> Forall wl_body_byte l.
Proof.
  intros [Hbody Hok].
  pose proof (wl_body_bytes (wl_words l) (line_ok_wf _ Hok)) as Hfb.
  by rewrite Hbody in Hfb.
Qed.

Lemma body_ok_short l : body_ok l -> (S (length l) < line_max)%nat.
Proof.
  intros [Hbody Hok]. pose proof (line_ok_len _ Hok) as Hlen.
  rewrite wl_line_length Hbody in Hlen. lia.
Qed.

(* D3, THE CONTENT HALF OF THE DISCIPLINE, at a line per round: every
   COMPLETE body of the era's input is an admissible line, and the partial
   line the user is in the middle of is body bytes, short enough that its
   newline will still fit the buffer.

   THE PARTIAL LINE IS ONLY ASKED FOR BODY BYTES.  A malformed body stays
   disciplined until its newline, where [line_ok] fails and the taint
   fires; that is sound, and it is what keeps prefix closure a one-liner
   ([disc_input_snoc]). *)
Definition disc_input (I : list (bv 8)) : Prop :=
  Forall body_ok (bodies_of I)
  /\ Forall wl_body_byte (rest_of I)
  /\ (S (length (rest_of I)) < line_max)%nat.

Global Instance disc_input_dec I : Decision (disc_input I).
Proof. rewrite /disc_input. apply _. Defined.

Lemma disc_input_nil : disc_input [].
Proof.
  rewrite /disc_input bodies_of_nil rest_of_nil /line_max.
  split; [constructor |]. split; [constructor | cbn [length]; lia].
Qed.

Lemma disc_input_snoc I b : disc_input (I ++ [b]) -> disc_input I.
Proof.
  intros (Hb & Hr & Hs). destruct (decide (b = wl_nl)) as [-> | Hne].
  - rewrite bodies_of_snoc_nl in Hb.
    apply Forall_app in Hb as [Hb1 Hb2]. rewrite Forall_singleton in Hb2.
    split; [exact Hb1 |]. split; [exact (body_ok_bytes _ Hb2) |].
    exact (body_ok_short _ Hb2).
  - rewrite (bodies_of_snoc_other I b Hne) in Hb.
    rewrite (rest_of_snoc_other I b Hne) in Hr, Hs.
    apply Forall_app in Hr as [Hr1 _].
    split; [exact Hb |]. split; [exact Hr1 |].
    rewrite (length_app (rest_of I) [b]) in Hs. cbn [length] in Hs. lia.
Qed.

Lemma disc_input_prefix I I' :
  I `prefix_of` I' -> disc_input I' -> disc_input I.
Proof.
  intros [k ->]. induction k as [| b k IH] using rev_ind; intro Hd.
  - by rewrite app_nil_r in Hd.
  - apply IH. rewrite app_assoc in Hd. exact (disc_input_snoc _ _ Hd).
Qed.

Lemma disc_input_body I i l :
  disc_input I -> bodies_of I !! i = Some l -> body_ok l.
Proof. intros (Hb & _ & _) Hi. exact (Forall_lookup_1 _ _ _ _ Hb Hi). Qed.

Lemma disc_input_line I i l :
  disc_input I -> bodies_of I !! i = Some l ->
  l = wl_body (wl_words l) /\ line_ok (wl_words l).
Proof.
  intros Hd Hi. destruct (disc_input_body I i l Hd Hi) as [Hbody Hok].
  split; [by rewrite Hbody | exact Hok].
Qed.

Lemma disc_input_rest_short I :
  disc_input I -> (S (length (rest_of I)) < line_max)%nat.
Proof. by intros (_ & _ & H). Qed.

(* the input IS the lines it parses to, which is how a proof that knows the
   words rebuilds the wire *)
Lemma body_ok_words_fmap bs :
  Forall body_ok bs -> wl_body <$> (wl_words <$> bs) = bs.
Proof.
  induction bs as [| l bs IH]; intro HF; [done |].
  destruct (Forall_cons_1 _ _ _ HF) as [[Hb _] HF'].
  by rewrite !fmap_cons Hb (IH HF').
Qed.

Lemma disc_input_join I :
  disc_input I -> I = wl_lines (wl_words <$> bodies_of I) ++ rest_of I.
Proof.
  intros (Hb & _ & _).
  rewrite -wl_lines_join (body_ok_words_fmap _ Hb). exact (wl_cut_join I).
Qed.

(* ---- EVERY BYTE OF A DISCIPLINED INPUT, NUMERICALLY ------------------- *)
(* The console-side proofs each have to refute one byte -- the carriage
   return [consoleintr] rewrites, the three erase characters, the
   end-of-file byte, the NUL [gets] plants past the line.  All of them come
   off this one reading by [lia], at any line. *)
Lemma join_elem_of (bs : list (list (bv 8))) (b : bv 8) :
  b ∈ wl_join bs -> b = wl_nl \/ exists l, l ∈ bs /\ b ∈ l.
Proof.
  induction bs as [| l bs IH]; intro Hb.
  { rewrite wl_join_nil in Hb. by apply elem_of_nil in Hb. }
  rewrite wl_join_cons in Hb. apply elem_of_app in Hb as [Hb | Hb].
  - right. exists l. split; [apply list_elem_of_here | exact Hb].
  - apply elem_of_cons in Hb as [-> | Hb]; [by left |].
    destruct (IH Hb) as [-> | (l' & Hl' & Hb')]; [by left |].
    right. exists l'. split; [by apply list_elem_of_further | exact Hb'].
Qed.

Lemma disc_input_byte I b :
  disc_input I -> b ∈ I -> wl_body_byte b \/ b = wl_nl.
Proof.
  intros Hd Hin. pose proof Hd as (Hb & Hr & _).
  rewrite (wl_cut_join I) in Hin.
  apply elem_of_app in Hin as [Hin | Hin].
  - destruct (join_elem_of (bodies_of I) b Hin) as [-> | (l & Hl & Hbl)];
      [by right | left].
    apply list_elem_of_lookup in Hl as [k Hk].
    destruct (disc_input_body I k l Hd Hk) as [Hbody Hok].
    pose proof (wl_body_bytes (wl_words l) (line_ok_wf _ Hok)) as Hfb.
    rewrite Hbody in Hfb.
    exact (proj1 (Forall_forall _ _) Hfb b Hbl).
  - left. exact (proj1 (Forall_forall _ _) Hr b Hin).
Qed.

Lemma disc_input_byte_val I b :
  disc_input I -> b ∈ I ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof.
  intros Hd Hin. destruct (disc_input_byte I b Hd Hin) as [[Ha | ->] | ->].
  - destruct Ha as [H | [H | H]];
      [ right; right; by left
      | right; right; right; by left
      | right; right; right; by right ].
  - right. left. exact wl_sp_val.
  - left. exact wl_nl_val.
Qed.

Lemma disc_input_byte_val_at I j :
  disc_input I -> (j < length I)%nat ->
  bv_unsigned (I !!! j) = 10%Z \/ bv_unsigned (I !!! j) = 32%Z
  \/ (48 <= bv_unsigned (I !!! j) <= 57)%Z
  \/ (65 <= bv_unsigned (I !!! j) <= 90)%Z
  \/ (97 <= bv_unsigned (I !!! j) <= 122)%Z.
Proof.
  intros Hd Hj. apply (disc_input_byte_val I _ Hd).
  destruct (lookup_lt_is_Some_2 I j Hj) as [b Hb].
  rewrite list_lookup_total_alt Hb. cbn [default from_option].
  exact (list_elem_of_lookup_2 I j b Hb).
Qed.

Lemma disc_input_byte_ncr I j :
  disc_input I -> (j < length I)%nat -> bv_unsigned (I !!! j) <> 13%Z.
Proof. intros Hd Hj. pose proof (disc_input_byte_val_at I j Hd Hj). lia. Qed.

Lemma disc_input_byte_nonzero I j :
  disc_input I -> (j < length I)%nat -> bv_unsigned (I !!! j) <> 0%Z.
Proof. intros Hd Hj. pose proof (disc_input_byte_val_at I j Hd Hj). lia. Qed.

(* THE NEWLINE CLOSES A LINE: a disciplined input ending in one has an
   empty rest, and the body it just completed is an admissible line.  This
   is what the shell's read link hands its caller in place of "the buffer
   holds THE line". *)
Lemma disc_input_snoc_nl I : disc_input (I ++ [wl_nl]) -> body_ok (rest_of I).
Proof.
  intros (Hb & _ & _). rewrite bodies_of_snoc_nl in Hb.
  apply Forall_app in Hb as [_ Hb2]. by rewrite Forall_singleton in Hb2.
Qed.

Lemma disc_input_last_ws I :
  disc_input (I ++ [wl_nl]) ->
  line_ok (last_ws (I ++ [wl_nl]))
  /\ wl_body (last_ws (I ++ [wl_nl])) = rest_of I.
Proof.
  intro Hd. destruct (disc_input_snoc_nl I Hd) as [Hbody Hok].
  rewrite last_ws_snoc_nl. split; [exact Hok | exact Hbody].
Qed.

(* the round counters at the empty input, and the round-is-complete test
   without arithmetic: a nonempty input whose rest is empty has closed at
   least one line *)
Lemma nlines_nil : nlines [] = 0%nat.
Proof. rewrite /nlines bodies_of_nil. reflexivity. Qed.

Lemma nstarted_nil : nstarted [] = 0%nat.
Proof.
  rewrite /nstarted nlines_nil rest_of_nil. case_decide as H; [done |].
  by destruct (H eq_refl).
Qed.

Lemma nlines_pos_of_rest_nil I :
  I <> [] -> rest_of I = [] -> (1 <= nlines I)%nat.
Proof.
  intros Hne Hr. destruct (rest_of_end I Hr) as [-> | Hl]; [done |].
  destruct I as [| b J _] using rev_ind; [done |].
  rewrite last_snoc in Hl. injection Hl as Hb. subst b.
  rewrite nlines_snoc_nl. lia.
Qed.

(* the INPUT bytes of an observation list, in order -- the CONSOLE's; an
   input on the other port is not the user's and is invisible here.  It IS
   [ObsTrace.obs_ins] at [Uart0], which is the name the KERNEL's boundary
   contract counts inputs by ([ConsLog.cons_ev_ok]'s log-completeness
   clause), so the two sides of that contract are the same function and
   [ins_obs_ins] is the identity. *)
Definition ins (h : list mobs) : list (bv 8) := obs_ins Uart0 h.

Lemma ins_obs_ins (h : list mobs) : ins h = obs_ins Uart0 h.
Proof. reflexivity. Qed.

Lemma ins_app (h k : list mobs) : ins (h ++ k) = ins h ++ ins k.
Proof. exact (obs_ins_app Uart0 h k). Qed.

Lemma ins_in (b : bv 8) : ins [ObsUartIn Uart0 b] = [b].
Proof. exact (obs_ins_in Uart0 b). Qed.
Lemma ins_out (b : bv 8) : ins [ObsUartOut Uart0 b] = [].
Proof. exact (obs_ins_out Uart0 Uart0 b). Qed.

Lemma ins_prefix (s1 s2 : list mobs) :
  s1 `prefix_of` s2 -> ins s1 `prefix_of` ins s2.
Proof. intros [z ->]. rewrite ins_app. by eexists. Qed.

(* D3 OVER ONE POWER CYCLE'S INPUT.  Everything the tree states about the
   content of what was typed reads off this. *)
Definition disc_seg (seg : list mobs) : Prop := disc_input (ins seg).

Global Instance disc_seg_dec seg : Decision (disc_seg seg).
Proof. rewrite /disc_seg. apply _. Defined.

Lemma disc_seg_nil : disc_seg [].
Proof. exact disc_input_nil. Qed.

Lemma disc_seg_out (seg : list mobs) (b : bv 8) :
  disc_seg (seg ++ [ObsUartOut Uart0 b]) <-> disc_seg seg.
Proof. rewrite /disc_seg ins_app ins_out app_nil_r. done. Qed.

Lemma disc_seg_prefix (seg' seg : list mobs) :
  seg' `prefix_of` seg -> disc_seg seg -> disc_seg seg'.
Proof.
  intros [k ->] Hd. rewrite /disc_seg ins_app in Hd.
  apply (disc_input_prefix _ _ ltac:(by eexists) Hd).
Qed.

(* the one generic fact about a repeated pattern still spent below, by the
   restart loop's [pro_fail] *)
Lemma concat_replicate_S {A} (n : nat) (pat : list A) :
  concat (replicate (S n) pat) = concat (replicate n pat) ++ pat.
Proof. by rewrite replicate_S_end concat_app /= app_nil_r. Qed.

(* ====================================================================== *)
(*  2.  THE EXPECTED SESSION (R3, with O5's alternatives)                  *)
(* ====================================================================== *)

(* ---- 2a.  THE PROLOGUE, AND ITS ALTERNATIVES ---- *)

(* user/init.c:27, user/sh.c:137, user/init.c:35 and user/init.c:30 -- the
   four literals the console's opening is made of.  Every one is a console
   write ([printf] to fd 1, [fprintf] to fd 2, on descriptors init opened on
   "console"), so every one reaches THIS wire. *)
Definition u_banner   : list (bv 8) := sb "init: starting sh"%string ++ nlb.
Definition u_prompt   : list (bv 8) := sb "$ "%string.
Definition u_execfail : list (bv 8) := sb "init: exec sh failed"%string ++ nlb.
Definition u_forkfail : list (bv 8) := sb "init: fork failed"%string ++ nlb.

(* THE GOOD PROLOGUE, kept under its own name and byte for byte what it was:
   init's banner, then sh's first prompt. *)
Definition u_prologue : list (bv 8) :=
  sb "init: starting sh"%string ++ nlb ++ sb "$ "%string.

(* THE PROLOGUE ALTERNATIVES, RULED BY THE OWNER (2026-09-16: "allow these
   errors in the top-level trace theorem"; 2026-09-14: "the banner is
   optional ... a trace without a banner in a given era has to be possible
   anyway").  A prologue round is a SEQUENCE OF LETTERS, each a console
   write of init's or the shell's, and the round's transcript is the
   concatenation of their bytes:
     0  "$ "                       sh runs: the session begins.  ENDS the
                                   round.
     1  "init: exec sh failed\n"   the child could not exec (user/init.c:35);
                                   it exits, init's wait reaps it and the
                                   outer loop runs AGAIN.  CONTINUES.
     2  "init: fork failed\n"      init could not fork (user/init.c:30); it
                                   exits and kexit panics (kernel/proc.c:339)
                                   on the OTHER port, so no PROCESS ever
                                   writes this wire again.  ENDS the round.
     3  "init: starting sh\n"      init's banner (user/init.c:27), printed at
                                   the head of every turn of its outer loop
                                   WHEN ITS CONSOLE IS OPEN.  CONTINUES.
   THE BANNER IS A LETTER AND NOT A PREFIX OF THE OTHERS because init's
   console open can fail (the kernel's open contract admits a full file
   table) while the shell's own opens succeed: init then prints nothing at
   all and the round is "$ " alone -- the resolution [[0]] -- where a
   round with the banner is [[3; 0]].  The good run is [[3; 0]]; one exec
   failure and a restart is [[3; 1; 3; 0]]; the fork failure is [[3; 2]].

   WHY THE LETTERS ARE FILED ONE AT A TIME.  A writer's knowledge of the
   round is a persistent LOWER BOUND of the resolution ([EchoOut.ps_lb]),
   and a lower bound is worth exactly the bytes of the letters it names
   ([pro_of_mono]): an open round predicts NOTHING beyond them.  An
   alternative whose transcript RETRACTED a default (a "prompt without the
   banner" filed against a round that predicted the banner) would make a
   stale bound predict bytes the wire will never carry, and then no link
   stated at a lower bound could be proved.  So the banner is what init
   files when it writes its first banner byte, and nothing is predicted
   before that.

   Their first bytes are '$', 'i', 'i', 'i' -- NOT pairwise distinct, so no
   one-byte reading of the resolution is available; what they are is
   PAIRWISE PREFIX-FREE (the three diagnostics part at byte 6,
   "init: e" / "init: f" / "init: s"), and that whole-block reading is
   what pins the resolution off the wire ([pro_of_prefix_free]).  A later
   ruling changes this ONE list.

   NOT HERE: "init: wait returned an error\n" (user/init.c:47).  That arm is
   REFUTED and not admitted -- kwait returns -1 only for a caller with no
   children or a killed one, and init holds the shell's generation. *)
Definition pro_alts : list (list (bv 8)) :=
  [ u_prompt; u_execfail; u_forkfail; u_banner ].

Lemma pro_alts_length : length pro_alts = 4.
Proof. reflexivity. Qed.

(* the letters that CONTINUE a round: the exec failure and the banner *)
Definition pro_cont (a : nat) : Prop := a = 1%nat \/ a = 3%nat.

Global Instance pro_cont_dec a : Decision (pro_cont a).
Proof. rewrite /pro_cont. apply _. Defined.

(* THE PROLOGUE FOR A RESOLUTION [ps]: the letters' bytes, in order, up to
   and including the first letter that ENDS the round; what follows it
   belongs to the next round.  OUT OF LETTERS the prologue is what has been
   filed and nothing more, so [pro_of] is MONOTONE under append
   ([pro_of_snoc]) -- which is exactly what a writer's mono_list LOWER
   BOUND of [ps] is worth -- and a COMPLETE prologue is one whose [ps] has
   an ending letter ([pro_done]).  [pro_of] reads exactly ONE round: it
   discards the tail at the first ending letter, so the r-th round's
   prologue is [pro_of (pro_from r ps)]. *)
Definition pro_more (a : nat) (t : list (bv 8)) : list (bv 8) :=
  if decide (pro_cont a) then t else [].

Fixpoint pro_of (ps : list nat) : list (bv 8) :=
  match ps with
  | [] => []
  | a :: ps' => pro_alts !!! a ++ pro_more a (pro_of ps')
  end.

Definition pro_done (ps : list nat) : Prop := Exists (fun a => ~ pro_cont a) ps.

Global Instance pro_done_dec ps : Decision (pro_done ps).
Proof. rewrite /pro_done. apply _. Defined.

(* drop ONE round, and [r] of them *)
Fixpoint pro_tail (ps : list nat) : list nat :=
  match ps with
  | [] => []
  | a :: ps' => if decide (pro_cont a) then pro_tail ps' else ps'
  end.

Fixpoint pro_from (r : nat) (ps : list nat) : list nat :=
  match r with
  | 0%nat => ps
  | S r' => pro_from r' (pro_tail ps)
  end.

(* how many rounds [ps] has SETTLED: one per ending letter *)
Fixpoint pro_rounds (ps : list nat) : nat :=
  match ps with
  | [] => 0%nat
  | a :: ps' => ((if decide (pro_cont a) then 0 else 1) + pro_rounds ps')%nat
  end.

(* one failed sub-round of the restart loop, in wire bytes: banner + the
   exec diagnostic *)
Definition pro_round : nat := (length u_banner + length u_execfail)%nat.

(* [j] FAILED SUB-ROUNDS: banner, exec failure, banner, exec failure, ...
   -- the open round init's restart head stands in *)
Definition pro_fail (j : nat) : list nat := concat (replicate j [3%nat; 1%nat]).

Lemma pro_more_cont (a : nat) (t : list (bv 8)) : pro_cont a -> pro_more a t = t.
Proof. intros H. rewrite /pro_more. by rewrite decide_True. Qed.

Lemma pro_more_1 (t : list (bv 8)) : pro_more 1%nat t = t.
Proof. apply pro_more_cont. by left. Qed.

Lemma pro_more_3 (t : list (bv 8)) : pro_more 3%nat t = t.
Proof. apply pro_more_cont. by right. Qed.

Lemma pro_more_ne (a : nat) (t : list (bv 8)) : ~ pro_cont a -> pro_more a t = [].
Proof. intros H. rewrite /pro_more. by rewrite decide_False. Qed.

Lemma pro_cont_ne (a : nat) : a <> 1%nat -> a <> 3%nat -> ~ pro_cont a.
Proof. intros H1 H3 [H | H]; [exact (H1 H) | exact (H3 H)]. Qed.

Lemma u_banner_pos : (0 < length u_banner)%nat.
Proof. vm_compute. lia. Qed.

Lemma pro_of_nil : pro_of [] = [].
Proof. reflexivity. Qed.

Lemma pro_of_cons (a : nat) (ps : list nat) :
  pro_of (a :: ps) = pro_alts !!! a ++ pro_more a (pro_of ps).
Proof. reflexivity. Qed.

Lemma pro_of_good : pro_of [3%nat; 0%nat] = u_prologue.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ...and the banner-less good run, the ruling's own case *)
Lemma pro_of_good_noban : pro_of [0%nat] = u_prompt.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* every letter is at least two bytes *)
Lemma pro_alts_nonnil (a : nat) : (a < length pro_alts)%nat -> pro_alts !!! a <> [].
Proof.
  rewrite pro_alts_length. intros Ha.
  destruct a as [|[|[|[|a]]]]; try lia; vm_compute; discriminate.
Qed.

Lemma pro_of_pos (ps : list nat) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> ps <> [] ->
  (0 < length (pro_of ps))%nat.
Proof.
  intros HF Hne. destruct ps as [| a ps]; [done |].
  rewrite Forall_cons in HF. destruct HF as [Ha _].
  cbn [pro_of]. rewrite length_app.
  destruct (pro_alts !!! a) as [| z zs] eqn:Hz;
    [ exfalso; exact (pro_alts_nonnil a Ha Hz) | cbn; lia ].
Qed.

(* the letters of an OPEN round all continue it *)
Lemma pro_open_cont (ps : list nat) : ~ pro_done ps -> Forall pro_cont ps.
Proof.
  induction ps as [| c ps IH]; intros Hnd; [done |].
  rewrite Forall_cons. split.
  - destruct (decide (pro_cont c)) as [? | Hne]; [done |].
    exfalso. apply Hnd. rewrite /pro_done. by apply Exists_cons; left.
  - apply IH. intros H. apply Hnd. rewrite /pro_done Exists_cons. by right.
Qed.

(* ...so [pro_of] is a HOMOMORPHISM on it: filing anything after an open
   round appends the bytes *)
Lemma pro_of_open_app (ps z : list nat) :
  ~ pro_done ps -> pro_of (ps ++ z) = pro_of ps ++ pro_of z.
Proof.
  intros Hnd. pose proof (pro_open_cont ps Hnd) as HF. clear Hnd.
  induction ps as [| c ps IH]; [done |].
  rewrite Forall_cons in HF. destruct HF as [Hc HF].
  cbn [app pro_of]. rewrite !(pro_more_cont c _ Hc).
  rewrite (IH HF). by rewrite app_assoc.
Qed.

Lemma pro_of_singleton (a : nat) : pro_of [a] = pro_alts !!! a.
Proof.
  cbn [pro_of]. rewrite /pro_more. case_decide; by rewrite app_nil_r.
Qed.

(* ---- [pro_of] is monotone in the resolution ---- *)

Lemma pro_of_snoc ps a : pro_of ps `prefix_of` pro_of (ps ++ [a]).
Proof.
  induction ps as [| c ps IH]; cbn [pro_of app].
  - apply prefix_nil.
  - destruct (decide (pro_cont c)) as [Hc | Hc].
    + rewrite !(pro_more_cont c _ Hc). by apply prefix_app.
    + rewrite !(pro_more_ne c _ Hc). reflexivity.
Qed.

Lemma pro_of_mono ps ps' : ps `prefix_of` ps' -> pro_of ps `prefix_of` pro_of ps'.
Proof.
  intros [z ->]. induction z as [| a z IH] using rev_ind.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. etrans; [exact IH | apply pro_of_snoc].
Qed.

Lemma pro_of_done_ext ps ps' :
  ps `prefix_of` ps' -> pro_done ps -> pro_of ps = pro_of ps'.
Proof.
  intros [z ->]. induction ps as [| a ps IH]; intros Hd.
  - by apply Exists_nil in Hd.
  - rewrite /pro_done Exists_cons in Hd.
    cbn [app pro_of]. destruct (decide (pro_cont a)) as [Ha | Ha].
    + rewrite !(pro_more_cont a _ Ha).
      destruct Hd as [Hne | Hd]; [done |]. by rewrite (IH Hd).
    + by rewrite !(pro_more_ne a _ Ha).
Qed.

Lemma pro_tail_mono ps ps' : ps `prefix_of` ps' -> pro_tail ps `prefix_of` pro_tail ps'.
Proof.
  intros [z ->]. induction ps as [| a ps IH]; cbn [app pro_tail].
  - apply prefix_nil.
  - case_decide; [exact IH | by eexists].
Qed.

Lemma pro_from_mono r ps ps' :
  ps `prefix_of` ps' -> pro_from r ps `prefix_of` pro_from r ps'.
Proof.
  revert ps ps'. induction r as [| r IH]; intros ps ps' Hp; [exact Hp |].
  cbn [pro_from]. by apply IH, pro_tail_mono.
Qed.

Lemma pro_of_from_mono r ps ps' :
  ps `prefix_of` ps' -> pro_of (pro_from r ps) `prefix_of` pro_of (pro_from r ps').
Proof. intros Hp. by apply pro_of_mono, pro_from_mono. Qed.

Lemma pro_tail_Forall (P : nat -> Prop) ps : Forall P ps -> Forall P (pro_tail ps).
Proof.
  induction ps as [| a ps IH]; cbn [pro_tail]; [done |].
  rewrite Forall_cons. intros [Ha Hps]. case_decide; [by apply IH | exact Hps].
Qed.

(* a settled round stays settled under extension *)
Lemma pro_done_mono ps ps' : ps `prefix_of` ps' -> pro_done ps -> pro_done ps'.
Proof. intros [z ->] Hd. rewrite /pro_done Exists_app. by left. Qed.

(* ---- how many rounds a resolution has settled ---- *)

Lemma pro_rounds_tail ps : pro_rounds (pro_tail ps) = (pro_rounds ps - 1)%nat.
Proof.
  induction ps as [| a ps IH]; cbn [pro_tail pro_rounds]; [done |].
  case_decide as Ha; [rewrite IH |]; lia.
Qed.

Lemma pro_done_rounds ps : pro_done ps <-> (0 < pro_rounds ps)%nat.
Proof.
  rewrite /pro_done. induction ps as [| a ps IH]; cbn [pro_rounds].
  - split; [by intros ?%Exists_nil | lia].
  - rewrite Exists_cons IH. case_decide as Ha.
    + split; [intros [H | H]; [by destruct (H Ha) | lia] | intros H; right; lia].
    + split; [intros _; lia | intros _; by left].
Qed.

Lemma pro_from_done r ps : pro_done (pro_from r ps) <-> (r < pro_rounds ps)%nat.
Proof.
  revert ps. induction r as [| r IH]; intros ps; cbn [pro_from].
  - rewrite pro_done_rounds. lia.
  - rewrite IH pro_rounds_tail. lia.
Qed.

Lemma pro_rounds_app ps ps' :
  pro_rounds (ps ++ ps') = (pro_rounds ps + pro_rounds ps')%nat.
Proof.
  induction ps as [| a ps IH]; cbn [app pro_rounds]; [done |].
  rewrite IH. case_decide; lia.
Qed.

Lemma pro_rounds_replicate_0 d : pro_rounds (replicate d 0%nat) = d.
Proof.
  induction d as [| d IH]; cbn [replicate pro_rounds]; [done |].
  rewrite IH. case_decide as H; [| lia]. exfalso. by destruct H.
Qed.

(* an open round's letters count no round, and the ending letter after
   them counts one *)
Lemma pro_rounds_open (g : list nat) : Forall pro_cont g -> pro_rounds g = 0%nat.
Proof.
  induction g as [| a g IH]; [done |].
  rewrite Forall_cons. intros [Ha Hg]. cbn [pro_rounds].
  rewrite decide_True; [| exact Ha]. by rewrite IH.
Qed.

Lemma pro_rounds_group (g : list nat) (t : nat) (z : list nat) :
  Forall pro_cont g -> ~ pro_cont t ->
  pro_rounds (g ++ [t] ++ z) = S (pro_rounds z).
Proof.
  intros Hg Ht. rewrite !pro_rounds_app (pro_rounds_open g Hg).
  cbn [pro_rounds]. rewrite decide_False; [lia | exact Ht].
Qed.

Lemma pro_of_from_done_ext r ps ps' :
  ps `prefix_of` ps' -> (r < pro_rounds ps)%nat ->
  pro_of (pro_from r ps) = pro_of (pro_from r ps').
Proof.
  intros Hp Hr. apply pro_of_done_ext; [by apply pro_from_mono |].
  by apply pro_from_done.
Qed.

(* ---- the four letters are PAIRWISE PREFIX-FREE ---- *)

Lemma pro_alts_prefix_det (a b : nat) :
  (a < length pro_alts)%nat -> (b < length pro_alts)%nat ->
  pro_alts !!! a `prefix_of` pro_alts !!! b -> a = b.
Proof.
  rewrite pro_alts_length. intros Ha Hb.
  destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; try lia;
    try reflexivity;
    intros H; exfalso; revert H; apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* THE WHOLE-BLOCK READING that a one-byte one cannot give: two
   resolutions below ONE wire have the SAME prologue, and a settled
   one below any forces the other settled too.  This is the ONE fact the
   reconciliation of the discipline's witness with the claim's spends. *)
Lemma pro_of_prefix_free (ps ps' : list nat) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  Forall (fun a => (a < length pro_alts)%nat) ps' -> pro_done ps' ->
  pro_of ps' `prefix_of` pro_of ps -> pro_done ps /\ pro_of ps' = pro_of ps.
Proof.
  revert ps. induction ps' as [| a' t' IH]; intros ps HF HF' Hd Hp.
  { by apply Exists_nil in Hd. }
  rewrite Forall_cons in HF'. destruct HF' as [Ha' HF'].
  rewrite /pro_done Exists_cons in Hd.
  destruct ps as [| a t].
  { exfalso. cbn [pro_of] in Hp.
    apply prefix_nil_inv, app_eq_nil in Hp as [Hnil _].
    exact (pro_alts_nonnil a' Ha' Hnil). }
  rewrite Forall_cons in HF. destruct HF as [Ha HF].
  cbn [pro_of] in Hp |- *.
  assert (Hcmp : pro_alts !!! a' `prefix_of` pro_alts !!! a
                 \/ pro_alts !!! a `prefix_of` pro_alts !!! a').
  { eapply prefix_weak_total;
      [ etrans; [apply prefix_app_r; reflexivity | exact Hp]
      | apply prefix_app_r; reflexivity ]. }
  assert (Haa : a' = a).
  { destruct Hcmp as [Hc | Hc];
      [ by apply pro_alts_prefix_det | symmetry; by apply pro_alts_prefix_det ]. }
  subst a'. apply prefix_app_inv in Hp.
  destruct (decide (pro_cont a)) as [Hc | Hc].
  - rewrite !(pro_more_cont a _ Hc) in Hp |- *.
    destruct Hd as [Hne | Hd]; [done |].
    destruct (IH t HF HF' Hd Hp) as [Hdt Heq].
    split; [by apply Exists_cons; right | by rewrite Heq].
  - rewrite !(pro_more_ne a _ Hc) in Hp |- *.
    split; [by apply Exists_cons; left | reflexivity].
Qed.

(* AN UNSETTLED PROLOGUE ENDS AT A LETTER BOUNDARY, so the byte any longer
   prologue has just past it is the first byte of one of the four letters.
   Read with [pro_of_open_head] below, this is what refutes "the stage's
   prologue is still open while the wire shows a prompt". *)
Lemma lookup_app_shift {A} (u v : list A) (n : nat) :
  (u ++ v) !! (length u + n)%nat = v !! n.
Proof.
  rewrite lookup_app_r; [| lia].
  by replace (length u + n - length u)%nat with n by lia.
Qed.


Lemma pro_of_not_done_next (P P' : list nat) (b : bv 8) :
  Forall (fun a => (a < length pro_alts)%nat) P' ->
  ~ pro_done P ->
  pro_of P `prefix_of` pro_of P' ->
  pro_of P' !! length (pro_of P) = Some b ->
  exists a, (a < length pro_alts)%nat /\ pro_alts !!! a !! 0%nat = Some b.
Proof.
  revert P'. induction P as [| c P IH]; intros P' HF' Hnd Hpre Hlk.
  - destruct P' as [| a t'].
    { exfalso. cbn [pro_of] in Hlk. discriminate. }
    rewrite Forall_cons in HF'. destruct HF' as [Ha HF'].
    exists a. split; [exact Ha |].
    cbn [pro_of length] in Hlk.
    rewrite lookup_app_l in Hlk; [exact Hlk |].
    destruct (pro_alts !!! a) as [| z zs] eqn:Hz;
      [ exfalso; exact (pro_alts_nonnil a Ha Hz) | cbn; lia ].
  - assert (Hc1 : pro_cont c).
    { destruct (decide (pro_cont c)) as [? | Hne]; [done |].
      exfalso. apply Hnd. rewrite /pro_done. by apply Exists_cons; left. }
    assert (HndP : ~ pro_done P).
    { intros H. apply Hnd. rewrite /pro_done Exists_cons. by right. }
    destruct P' as [| a t'].
    { exfalso. cbn [pro_of] in Hpre. rewrite (pro_more_cont c _ Hc1) in Hpre.
      apply prefix_nil_inv, app_eq_nil in Hpre as [Hnil _].
      assert (Hcb : (c < length pro_alts)%nat)
        by (destruct Hc1 as [-> | ->]; rewrite pro_alts_length; lia).
      exact (pro_alts_nonnil c Hcb Hnil). }
    rewrite Forall_cons in HF'. destruct HF' as [Ha HF'].
    cbn [pro_of] in Hpre, Hlk. rewrite (pro_more_cont c _ Hc1) in Hpre, Hlk.
    assert (Hcb : (c < length pro_alts)%nat)
      by (destruct Hc1 as [-> | ->]; rewrite pro_alts_length; lia).
    assert (Haa : a = c).
    { destruct (prefix_weak_total (pro_alts !!! c) (pro_alts !!! a)
                  (pro_alts !!! a ++ pro_more a (pro_of t'))
                  ltac:(etrans; [apply prefix_app_r; reflexivity | exact Hpre])
                  ltac:(apply prefix_app_r; reflexivity)) as [H | H].
      - symmetry. apply pro_alts_prefix_det; [exact Hcb | exact Ha | exact H].
      - apply pro_alts_prefix_det; [exact Ha | exact Hcb | exact H]. }
    subst a. rewrite (pro_more_cont c _ Hc1) in Hpre, Hlk.
    apply prefix_app_inv in Hpre.
    apply (IH t' HF' HndP Hpre).
    rewrite (length_app (pro_alts !!! c) (pro_of P)) in Hlk.
    rewrite (lookup_app_shift (pro_alts !!! c)) in Hlk.
    exact Hlk.
Qed.

(* ---- WHAT A PROLOGUE'S FIRST BYTE CAN BE ---- *)

(* The prompt is the ONLY letter that opens on '$'; the other three are
   init's diagnostics and its banner, all of which open on 'i'.  That is
   the whole of what the block-level determinacy needs to tell a settled
   round from an open one when the wire shows a prompt
   ([EchoOutPure.alt_cont_prefix_det]). *)
Lemma u_prompt_head : u_prompt !! 0%nat = Some (Z_to_bv 8 36%Z).
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma u_prompt_pos : (0 < length u_prompt)%nat.
Proof. vm_compute. lia. Qed.

Lemma pro_alts_head_dollar (a : nat) (b : bv 8) :
  (a < length pro_alts)%nat -> pro_alts !!! a !! 0%nat = Some b ->
  bv_unsigned b = 36%Z -> a = 0%nat.
Proof.
  rewrite pro_alts_length. intros Ha Hb Hv.
  (* [lia] also closes the [a = 0] goal, so only the three refutations remain *)
  destruct a as [|[|[|[|a]]]]; try lia;
    exfalso; vm_compute in Hb; injection Hb as Hb;
    rewrite -Hb in Hv; vm_compute in Hv; lia.
Qed.

(* an OPEN round's first byte is a letter of [init:], never a prompt *)
Lemma pro_of_open_head (ps : list nat) (b : bv 8) :
  ~ pro_done ps -> pro_of ps !! 0%nat = Some b -> bv_unsigned b = 105%Z.
Proof.
  intros Hnd Hb. destruct ps as [| a ps']; [by cbn in Hb |].
  destruct (Forall_cons_1 _ _ _ (pro_open_cont _ Hnd)) as [Hc _].
  assert (Hab : (a < length pro_alts)%nat)
    by (destruct Hc as [-> | ->]; rewrite pro_alts_length; lia).
  assert (Hpos : (0 < length (pro_alts !!! a))%nat).
  { destruct (pro_alts !!! a) as [| z zs] eqn:Hz;
      [ exfalso; exact (pro_alts_nonnil a Hab Hz) | cbn [length]; lia ]. }
  rewrite pro_of_cons (lookup_app_l _ _ 0%nat Hpos) in Hb.
  destruct Hc as [-> | ->];
    vm_compute in Hb; injection Hb as Hb; rewrite -Hb; by vm_compute.
Qed.

Lemma pro_of_open_no_dollar (ps : list nat) (b : bv 8) :
  ~ pro_done ps -> b ∈ pro_of ps -> bv_unsigned b <> 36%Z.
Proof.
  intros Hnd Hb. pose proof (pro_open_cont ps Hnd) as HF. clear Hnd.
  assert (Hlet : forall a : nat, pro_cont a ->
            Forall (fun c : bv 8 => bv_unsigned c <> 36%Z) (pro_alts !!! a)).
  { intros a [-> | ->]; apply (bool_decide_unpack _); vm_compute; exact I. }
  revert b Hb. induction ps as [| a ps IH]; intros b Hb.
  { by apply elem_of_nil in Hb. }
  destruct (Forall_cons_1 _ _ _ HF) as [Hc HF'].
  rewrite pro_of_cons (pro_more_cont a _ Hc) in Hb.
  apply elem_of_app in Hb as [Hb | Hb].
  - exact (proj1 (Forall_forall _ _) (Hlet a Hc) b Hb).
  - exact (IH HF' b Hb).
Qed.

(* ...so a SETTLED prologue whose first byte is '$' IS the prompt: letter 0
   ends the round, so nothing follows it *)
Lemma pro_of_dollar_prompt (P : list nat) :
  Forall (fun a => (a < length pro_alts)%nat) P -> P <> [] ->
  (forall b, pro_of P !! 0%nat = Some b -> bv_unsigned b = 36%Z) ->
  pro_of P = u_prompt.
Proof.
  intros HF Hne Hd. destruct P as [| a P']; [done |].
  destruct (Forall_cons_1 _ _ _ HF) as [Ha _].
  assert (Hpos : (0 < length (pro_alts !!! a))%nat).
  { destruct (pro_alts !!! a) as [| z zs] eqn:Hz;
      [ exfalso; exact (pro_alts_nonnil a Ha Hz) | cbn [length]; lia ]. }
  destruct (lookup_lt_is_Some_2 (pro_alts !!! a) 0%nat Hpos) as [b Hb].
  assert (Hlk : pro_of (a :: P') !! 0%nat = Some b)
    by (rewrite pro_of_cons (lookup_app_l _ _ 0%nat Hpos); exact Hb).
  assert (Ha0 : a = 0%nat) by (apply (pro_alts_head_dollar a b Ha Hb), Hd, Hlk).
  subst a. rewrite pro_of_cons (pro_more_ne 0%nat _ ltac:(by intros [H | H])).
  by rewrite app_nil_r.
Qed.

(* ---- 2b.  THE LINE ALTERNATIVES AND THE BLOCK ---- *)

(* SH'S TWO DIAGNOSTICS ARE THEMSELVES WORD LINES -- alphanumeric words,
   single blanks, one closing newline.  That is not a coincidence to be
   worked around: it is exactly WHY they can collide with echo's output,
   and stating them in the same vocabulary is what turns the collision
   into a statement the parse settles. *)
Definition dg_exec : list (list (bv 8)) :=
  [ sb "exec"%string; sb "echo"%string; sb "failed"%string ].
Definition dg_fork : list (list (bv 8)) := [ sb "fork"%string ].

Lemma dg_exec_line : wl_line dg_exec = sb "exec echo failed"%string ++ nlb.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma dg_fork_line : wl_line dg_fork = sb "fork"%string ++ nlb.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* O5, RULED BY THE OWNER (2026-09-12): allocation failure PRINTS, and what
   it prints is valid output.  After a complete line's '\n' echo the
   continuation is ONE OF
     0  <the line's words, minus the command name>  echo ran
     1  "exec echo failed\n$ "            sh's child could not exec
                                          (user/sh.c:80); it exits 0
     2  "$ "                              the child died before printing
     3  "fork\n"                          sh's fork1 panicked
                                          (user/sh.c:194; panic prints
                                          "%s\n" to fd 2 and exits 1), so
                                          init reaps the SHELL and its outer
                                          loop starts a NEW ROUND -- whose
                                          exec or fork can fail exactly as
                                          round 0's can, which is why the
                                          restart is a fresh PROLOGUE and
                                          not part of this literal
   Alternatives 0, 1 and 2 end in "$ "; ALTERNATIVE 3 DOES NOT -- the
   prologue [alt_blk] appends after it supplies the prompt, or the fork
   diagnostic instead.  A later ruling changes this ONE list.

   THE THREE CONSTANT ONES GET NAMES so that the files that write them
   ([UkShDiag], [UShPanic]) never mention a line. *)
Definition alt_execfail : list (bv 8) := wl_line dg_exec ++ u_prompt.
Definition alt_prompt   : list (bv 8) := u_prompt.
Definition alt_panic    : list (bv 8) := wl_line dg_fork.

Lemma alt_execfail_string :
  alt_execfail = sb "exec echo failed"%string ++ nlb ++ sb "$ "%string.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma alt_panic_string : alt_panic = sb "fork"%string ++ nlb.
Proof. exact dg_fork_line. Qed.

(* ECHO'S OUTPUT IS THE LINE MINUS ITS COMMAND NAME.  echo prints its
   arguments joined by single spaces and closed by a newline -- which is
   exactly what [gets] read, with the first word dropped.  So the good
   alternative is not a literal transcribed beside the line: it is
   [wl_line] of the line's tail, and then the prompt sh writes once it has
   reaped.  A transcription error cannot make the two disagree, because
   there is only one of them. *)
Definition line_alts_of (ws : list (list (bv 8))) : list (list (bv 8)) :=
  [ wl_line (drop 1 ws) ++ u_prompt; alt_execfail; alt_prompt; alt_panic ].

Lemma line_alts_of_length ws : length (line_alts_of ws) = 4%nat.
Proof. reflexivity. Qed.

Lemma line_alts_of_0 ws :
  line_alts_of ws !!! 0%nat = wl_line (drop 1 ws) ++ u_prompt.
Proof. reflexivity. Qed.
Lemma line_alts_of_1 ws : line_alts_of ws !!! 1%nat = alt_execfail.
Proof. reflexivity. Qed.
Lemma line_alts_of_2 ws : line_alts_of ws !!! 2%nat = alt_prompt.
Proof. reflexivity. Qed.
Lemma line_alts_of_3 ws : line_alts_of ws !!! 3%nat = alt_panic.
Proof. reflexivity. Qed.

Lemma line_alts_of_nonnil ws a :
  (a < 4)%nat -> line_alts_of ws !!! a <> [].
Proof.
  intros Ha Hnil.
  assert (Hlen : length (line_alts_of ws !!! a) = 0%nat)
    by (rewrite Hnil; reflexivity).
  destruct a as [|[|[|[|a]]]]; try lia.
  - rewrite line_alts_of_0 (length_app (wl_line (drop 1 ws)) u_prompt) in Hlen.
    pose proof (wl_line_pos (drop 1 ws)) as Hp. lia.
  - rewrite line_alts_of_1 /alt_execfail
      (length_app (wl_line dg_exec) u_prompt) in Hlen.
    pose proof (wl_line_pos dg_exec) as Hp. lia.
  - rewrite line_alts_of_2 in Hlen. vm_compute in Hlen. lia.
  - rewrite line_alts_of_3 /alt_panic wl_line_length in Hlen. lia.
Qed.

(* the two collisions, read off the word list: a line that echoes back
   exactly one of sh's diagnostics *)
Lemma line_alts_of_exec ws :
  drop 1 ws = dg_exec -> line_alts_of ws !!! 0%nat = alt_execfail.
Proof. intro H. by rewrite line_alts_of_0 H. Qed.

Lemma line_alts_of_fork ws :
  drop 1 ws = dg_fork -> line_alts_of ws !!! 0%nat = alt_panic ++ u_prompt.
Proof. intro H. by rewrite line_alts_of_0 H. Qed.

(* '$' is not a byte any line carries, so a bare prompt is never the head
   of an echoed line -- the one comparison involving the output that needs
   no side condition at all. *)
Lemma line_head_not_dollar (ws : list (list (bv 8))) :
  wl_wf ws -> exists b, wl_line ws !! 0%nat = Some b /\ bv_unsigned b <> 36%Z.
Proof.
  intro Hwf.
  destruct (lookup_lt_is_Some_2 (wl_line ws) 0%nat (wl_line_pos ws)) as [b Hb].
  exists b. split; [exact Hb |].
  pose proof (wl_line_byte_val ws b Hwf (list_elem_of_lookup_2 _ _ _ Hb)). lia.
Qed.

Lemma line_prompt_not_out (ws : list (list (bv 8))) :
  wl_wf ws -> ~ (u_prompt `prefix_of` wl_line ws ++ u_prompt).
Proof.
  intros Hwf Hp.
  destruct (line_head_not_dollar ws Hwf) as (d & Hd & Hdv). apply Hdv.
  assert (H1 : (wl_line ws ++ u_prompt) !! 0%nat = Some d)
    by (rewrite lookup_app_l; [exact Hd | exact (wl_line_pos ws)]).
  assert (H2 : (wl_line ws ++ u_prompt) !! 0%nat = Some (Z_to_bv 8 36%Z))
    by (eapply prefix_lookup_Some; [exact u_prompt_head | exact Hp]).
  rewrite H1 in H2. injection H2 as H2. rewrite H2. by vm_compute.
Qed.

(* ---- WHICH ALTERNATIVE RAN, AS FAR AS THE BYTES SAY IT --------------- *)

(* The claim used to read the alternative off ONE byte of the wire, and
   then off PREFIX-FREENESS of the four alternatives under two
   inequalities on the word list ("you may type anything except echo fork
   and echo exec echo failed").  The owner's ruling of 2026-09-16 admits
   those two lines as well, so there is no exclusion left and no index to
   read: at [echo fork] the output "fork\n$ " IS the panic line followed by
   a bare prompt, and at [echo exec echo failed] it IS the exec
   diagnostic.  The observer cannot tell WHICH alternative ran, and does
   not need to -- the transcript is the same BYTES either way, which is
   what this table says and what [EchoOutPure]'s determinacy spends. *)
Local Lemma lab_head_ne (u v X X' : list (bv 8)) (b c : bv 8) :
  u !! 0%nat = Some b -> v !! 0%nat = Some c ->
  bv_unsigned b <> bv_unsigned c ->
  ~ ((u ++ X) `prefix_of` (v ++ X')).
Proof.
  intros Hu Hv Hbc Hp.
  assert (Hlu : (0 < length u)%nat) by (apply lookup_lt_Some in Hu; lia).
  assert (Hlv : (0 < length v)%nat) by (apply lookup_lt_Some in Hv; lia).
  assert (H1 : (u ++ X) !! 0%nat = Some b)
    by (rewrite lookup_app_l; [exact Hu | exact Hlu]).
  assert (H2 : (v ++ X') !! 0%nat = Some b)
    by (eapply prefix_lookup_Some; [exact H1 | exact Hp]).
  rewrite (lookup_app_l v X' 0%nat Hlv) Hv in H2. injection H2 as H2.
  apply Hbc. by rewrite H2.
Qed.

Lemma alt_execfail_head : alt_execfail !! 0%nat = Some (Z_to_bv 8 101%Z).
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma alt_prompt_head : alt_prompt !! 0%nat = Some (Z_to_bv 8 36%Z).
Proof. exact u_prompt_head. Qed.

Lemma alt_panic_head : alt_panic !! 0%nat = Some (Z_to_bv 8 102%Z).
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma line_alts_of_prefix_bytes (ws : list (list (bv 8))) (a b : nat)
    (X X' : list (bv 8)) :
  wl_wf (drop 1 ws) -> (a < 4)%nat -> (b < 4)%nat ->
  (line_alts_of ws !!! a ++ X) `prefix_of` (line_alts_of ws !!! b ++ X') ->
  a = b
  \/ (a <> 3%nat /\ b <> 3%nat /\ line_alts_of ws !!! a = line_alts_of ws !!! b)
  \/ (a = 0%nat /\ b = 3%nat /\ drop 1 ws = dg_fork)
  \/ (a = 3%nat /\ b = 0%nat /\ drop 1 ws = dg_fork).
Proof.
  intros Hwf Ha Hb Hp.
  assert (HE : wl_wf dg_exec)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HFk : wl_wf dg_fork)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  destruct (line_head_not_dollar (drop 1 ws) Hwf) as (d0 & Hd0 & Hd0v).
  assert (Hh0 : (wl_line (drop 1 ws) ++ u_prompt) !! 0%nat = Some d0)
    by (rewrite lookup_app_l; [exact Hd0 | exact (wl_line_pos _)]).
  assert (Hdz : bv_unsigned (Z_to_bv 8 36%Z) = 36%Z) by (by vm_compute).
  assert (Hd0d : bv_unsigned d0 <> bv_unsigned (Z_to_bv 8 36%Z))
    by (rewrite Hdz; exact Hd0v).
  assert (Hd0d' : bv_unsigned (Z_to_bv 8 36%Z) <> bv_unsigned d0)
    by (intro Hq; apply Hd0d; by rewrite Hq).
  destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; try lia;
    try (left; reflexivity); right.
  (* (0,1) and (1,0): the output would BE the exec diagnostic *)
  - left.
    rewrite line_alts_of_0 line_alts_of_1 /alt_execfail
            -(app_assoc (wl_line (drop 1 ws)) u_prompt X)
            -(app_assoc (wl_line dg_exec) u_prompt X') in Hp.
    destruct (wl_line_prefix_det _ _ _ _ Hwf HE Hp) as [Heq _].
    split; [done |]. split; [done |].
    by rewrite line_alts_of_0 line_alts_of_1 /alt_execfail Heq.
  (* (0,2): no line opens on '$' *)
  - exfalso. rewrite line_alts_of_0 line_alts_of_2 in Hp.
    exact (lab_head_ne _ _ X X' _ _ Hh0 alt_prompt_head Hd0d Hp).
  (* (0,3): the output would BE the fork diagnostic *)
  - right. left.
    rewrite line_alts_of_0 line_alts_of_3 /alt_panic
            -(app_assoc (wl_line (drop 1 ws)) u_prompt X) in Hp.
    destruct (wl_line_prefix_det _ _ _ _ Hwf HFk Hp) as [Heq _].
    by split; [| split].
  - left.
    rewrite line_alts_of_0 line_alts_of_1 /alt_execfail
            -(app_assoc (wl_line dg_exec) u_prompt X)
            -(app_assoc (wl_line (drop 1 ws)) u_prompt X') in Hp.
    destruct (wl_line_prefix_det _ _ _ _ HE Hwf Hp) as [Heq _].
    split; [done |]. split; [done |].
    by rewrite line_alts_of_0 line_alts_of_1 /alt_execfail Heq.
  (* (1,2), (1,3): closed letters, distinct first bytes *)
  - exfalso. rewrite line_alts_of_1 line_alts_of_2 in Hp.
    refine (lab_head_ne _ _ X X' _ _ alt_execfail_head alt_prompt_head _ Hp).
    vm_compute. lia.
  - exfalso. rewrite line_alts_of_1 line_alts_of_3 in Hp.
    refine (lab_head_ne _ _ X X' _ _ alt_execfail_head alt_panic_head _ Hp).
    vm_compute. lia.
  (* (2,0) *)
  - exfalso. rewrite line_alts_of_0 line_alts_of_2 in Hp.
    exact (lab_head_ne _ _ X X' _ _ alt_prompt_head Hh0 Hd0d' Hp).
  - exfalso. rewrite line_alts_of_1 line_alts_of_2 in Hp.
    refine (lab_head_ne _ _ X X' _ _ alt_prompt_head alt_execfail_head _ Hp).
    vm_compute. lia.
  - exfalso. rewrite line_alts_of_2 line_alts_of_3 in Hp.
    refine (lab_head_ne _ _ X X' _ _ alt_prompt_head alt_panic_head _ Hp).
    vm_compute. lia.
  (* (3,0): the fork diagnostic would BE the output *)
  - right. right.
    rewrite line_alts_of_0 line_alts_of_3 /alt_panic
            -(app_assoc (wl_line (drop 1 ws)) u_prompt X') in Hp.
    destruct (wl_line_prefix_det _ _ _ _ HFk Hwf Hp) as [Heq _].
    split; [done |]. split; [done |]. by rewrite Heq.
  - exfalso. rewrite line_alts_of_1 line_alts_of_3 in Hp.
    refine (lab_head_ne _ _ X X' _ _ alt_panic_head alt_execfail_head _ Hp).
    vm_compute. lia.
  - exfalso. rewrite line_alts_of_2 line_alts_of_3 in Hp.
    refine (lab_head_ne _ _ X X' _ _ alt_panic_head alt_prompt_head _ Hp).
    vm_compute. lia.
Qed.

(* ---- WHERE ECHO'S OUTPUT PUTS EACH WORD ------------------------------ *)
(* Argument [i] of the line is word [i - 1] of the TAIL, because echo does
   not print the command name.  These are the whole of the cursor a write
   chain over the words walks: where a word starts, what follows it while
   another word remains, and what follows the last one. *)
Definition out_cur (ws : list (list (bv 8))) (i : nat) : nat :=
  wl_off 0%nat (drop 1 ws) (i - 1).

Lemma ws_drop (ws : list (list (bv 8))) (i : nat) :
  (1 <= i)%nat -> drop 1 ws !! (i - 1)%nat = ws !! i.
Proof. intro Hi. rewrite lookup_drop. f_equal. lia. Qed.

(* the alternative opens with the output, and the prompt is past it *)
Lemma alt0_out ws (p : nat) :
  (p < length (wl_line (drop 1 ws)))%nat ->
  line_alts_of ws !!! 0%nat !! p = wl_line (drop 1 ws) !! p.
Proof.
  intro Hp. rewrite line_alts_of_0.
  exact (lookup_app_l (wl_line (drop 1 ws)) u_prompt p Hp).
Qed.

Lemma out_cur_S ws (i : nat) (w : list (bv 8)) :
  (1 <= i)%nat -> ws !! i = Some w ->
  out_cur ws (S i) = S (out_cur ws i + length w)%nat.
Proof.
  intros Hi Hw. rewrite /out_cur.
  replace (S i - 1)%nat with (S (i - 1)) by lia.
  exact (wl_off_S_at (drop 1 ws) 0%nat (i - 1)%nat w
           ltac:(rewrite ws_drop; [exact Hw | exact Hi])).
Qed.

Lemma out_cur_lt ws (i : nat) (w : list (bv 8)) (j : nat) :
  (1 <= i)%nat -> ws !! i = Some w -> (j <= length w)%nat ->
  (out_cur ws i + j < length (wl_line (drop 1 ws)))%nat.
Proof.
  intros Hi Hw Hj. rewrite /out_cur.
  exact (wl_off_lt_line (drop 1 ws) (i - 1)%nat w j
           ltac:(rewrite ws_drop; [exact Hw | exact Hi]) Hj).
Qed.

(* a separator follows a word while another argument remains... *)
Lemma out_sep ws (i : nat) (w : list (bv 8)) :
  (1 <= i)%nat -> ws !! i = Some w -> (S i < length ws)%nat ->
  line_alts_of ws !!! 0%nat !! (out_cur ws i + length w)%nat = Some wl_sp.
Proof.
  intros Hi Hw Hlt.
  assert (Hd : drop 1 ws !! (i - 1)%nat = Some w)
    by (rewrite ws_drop; [exact Hw | exact Hi]).
  rewrite (alt0_out ws (out_cur ws i + length w)%nat
             (out_cur_lt ws i w (length w) Hi Hw ltac:(lia))).
  rewrite /out_cur.
  apply (wl_line_sep (drop 1 ws) (i - 1)%nat w Hd).
  rewrite length_drop. lia.
Qed.

(* ...and the closing newline follows the last, which is where the output
   ends *)
Lemma out_last ws (i : nat) (w : list (bv 8)) :
  (1 <= i)%nat -> ws !! i = Some w -> S i = length ws ->
  S (out_cur ws i + length w)%nat = length (wl_line (drop 1 ws))
  /\ line_alts_of ws !!! 0%nat !! (out_cur ws i + length w)%nat = Some wl_nl.
Proof.
  intros Hi Hw Hlast.
  assert (Hd : drop 1 ws !! (i - 1)%nat = Some w)
    by (rewrite ws_drop; [exact Hw | exact Hi]).
  assert (Hend : (out_cur ws i + length w)%nat
                 = length (wl_body (drop 1 ws))).
  { rewrite /out_cur.
    rewrite (wl_off_last (drop 1 ws) 0%nat (i - 1)%nat w Hd
               ltac:(rewrite length_drop; lia)).
    lia. }
  split.
  - rewrite Hend wl_line_length. lia.
  - rewrite (alt0_out ws (out_cur ws i + length w)%nat
               (out_cur_lt ws i w (length w) Hi Hw ltac:(lia))).
    rewrite Hend. exact (wl_line_nl_at (drop 1 ws)).
Qed.

(* the alternative is the output and then the prompt, so its length is
   the output's plus two -- not a number *)
Lemma line_alts_of_0_length ws :
  length (line_alts_of ws !!! 0%nat)
  = (length (wl_line (drop 1 ws)) + 2)%nat.
Proof.
  rewrite line_alts_of_0 (length_app (wl_line (drop 1 ws)) u_prompt).
  by vm_compute (length u_prompt).
Qed.

(* ---- THE ALTERNATIVES' LENGTHS.  Three of the four are constants and
   are read by computation; the good one's is [line_alts_of_0_length]. ---- *)
Lemma line_alts_len1 (ws : list (list (bv 8))) :
  length (line_alts_of ws !!! 1%nat) = 19%nat.
Proof. rewrite line_alts_of_1. by vm_compute. Qed.

Lemma line_alts_len2_ (ws : list (list (bv 8))) :
  length (line_alts_of ws !!! 2%nat) = 2%nat.
Proof. rewrite line_alts_of_2. by vm_compute. Qed.

Lemma line_alts_len3 (ws : list (list (bv 8))) :
  length (line_alts_of ws !!! 3%nat) = 5%nat.
Proof. rewrite line_alts_of_3. by vm_compute. Qed.

(* every line alternative but the panic is at least the prompt long --
   at the GOOD one because the output ends in the prompt, whatever the
   line was *)
Lemma line_alts_len_ge2 (ws : list (list (bv 8))) (a : nat) :
  (a < 3)%nat -> (2 <= length (line_alts_of ws !!! a))%nat.
Proof.
  intros Ha. destruct a as [| [| [| a]]].
  - rewrite (line_alts_of_0_length ws). lia.
  - rewrite (line_alts_len1 ws). lia.
  - rewrite (line_alts_len2_ ws). lia.
  - exfalso. lia.
Qed.

(* ...and its last two bytes ARE the prompt *)
Lemma line_alts_dollar (ws : list (list (bv 8))) (a : nat) :
  (a < 3)%nat ->
  line_alts_of ws !!! a !! (length (line_alts_of ws !!! a) - 2)%nat
  = Some (u_prompt !!! 0%nat).
Proof.
  intros Ha. destruct a as [| [| [| a]]].
  - rewrite (line_alts_of_0_length ws) (line_alts_of_0 ws).
    replace (length (wl_line (drop 1 ws)) + 2 - 2)%nat
      with (length (wl_line (drop 1 ws))) by lia.
    rewrite lookup_app_r; [| lia]. rewrite Nat.sub_diag. by vm_compute.
  - rewrite (line_alts_len1 ws) line_alts_of_1. by vm_compute.
  - rewrite (line_alts_len2_ ws) line_alts_of_2. by vm_compute.
  - exfalso. lia.
Qed.

Lemma line_alts_space (ws : list (list (bv 8))) (a : nat) :
  (a < 3)%nat ->
  line_alts_of ws !!! a !! (length (line_alts_of ws !!! a) - 1)%nat
  = Some (u_prompt !!! 1%nat).
Proof.
  intros Ha. destruct a as [| [| [| a]]].
  - rewrite (line_alts_of_0_length ws) (line_alts_of_0 ws).
    replace (length (wl_line (drop 1 ws)) + 2 - 1)%nat
      with (length (wl_line (drop 1 ws)) + 1)%nat by lia.
    rewrite lookup_app_r; [| lia].
    replace (length (wl_line (drop 1 ws)) + 1
             - length (wl_line (drop 1 ws)))%nat with 1%nat by lia.
    by vm_compute.
  - rewrite (line_alts_len1 ws) line_alts_of_1. by vm_compute.
  - rewrite (line_alts_len2_ ws) line_alts_of_2. by vm_compute.
  - exfalso. lia.
Qed.


(* how many shells have already died on their own fork panic BEFORE line
   [i] -- so line [i], if it took alternative 3, opens round
   [S (pro_idx cs i)], and the block that closes line [q-1] reads round
   [pro_idx cs q], round 0 at the head of the transcript included. *)
Fixpoint pro_idx (cs : list nat) (i : nat) : nat :=
  match i with
  | 0%nat => 0%nat
  | S i' => (pro_idx cs i' + if decide (cs !!! i' = 3%nat) then 1 else 0)%nat
  end.

Lemma pro_idx_S cs i :
  pro_idx cs (S i)
  = (pro_idx cs i + if decide (cs !!! i = 3%nat) then 1 else 0)%nat.
Proof. reflexivity. Qed.

Lemma pro_idx_S3 cs i : cs !!! i = 3%nat -> pro_idx cs (S i) = S (pro_idx cs i).
Proof. intros H. rewrite pro_idx_S decide_True; [lia | exact H]. Qed.

Lemma pro_idx_Sne cs i : cs !!! i <> 3%nat -> pro_idx cs (S i) = pro_idx cs i.
Proof. intros H. rewrite pro_idx_S decide_False; [lia | exact H]. Qed.

Lemma pro_idx_mono cs i j : (i <= j)%nat -> (pro_idx cs i <= pro_idx cs j)%nat.
Proof.
  intros Hij. induction j as [| j IH].
  - assert (i = 0%nat) by lia. by subst i.
  - destruct (decide (i = S j)) as [-> | Hne]; [done |].
    rewrite pro_idx_S.
    assert (pro_idx cs i <= pro_idx cs j)%nat by (apply IH; lia).
    case_decide; lia.
Qed.

Lemma pro_idx_le cs i : (pro_idx cs i <= i)%nat.
Proof.
  induction i as [| i IH]; [cbn; lia |].
  rewrite pro_idx_S. case_decide; lia.
Qed.

(* ONE COMPLETED LINE'S OUTPUT: the echo of the RAW BODY the console put
   back, the newline that closed it, the continuation this run took, and --
   if that continuation was the shell's own fork panic -- the PROLOGUE of
   the round init then starts.  [bs] is the list of complete bodies the
   era's input parses to ([LineWords.bodies_of]), [cs] records the
   continuation per line and [ps] the prologue choices of the whole run, in
   wire order; out of range all three read as their inhabitant, which keeps
   [alt_seq] total and its step law unconditional -- the choices are pinned
   by the wire wherever the discipline actually looks at them.

   THE ECHO HALF IS THE RAW BODY and not [wl_line] of its words: the
   console echoes what was typed, whether or not it parses, so the
   transcript grows with the input UNCONDITIONALLY ([sess_step]).  The
   parse feeds only the ALTERNATIVE. *)
Definition alt_cont (ps cs : list nat) (bs : list (list (bv 8))) (i : nat)
  : list (bv 8) :=
  line_alts_of (wl_words (bs !!! i)) !!! (cs !!! i)
  ++ (if decide (cs !!! i = 3%nat)
      then pro_of (pro_from (S (pro_idx cs i)) ps) else []).

Definition alt_blk (ps cs : list nat) (bs : list (list (bv 8))) (i : nat)
  : list (bv 8) :=
  bs !!! i ++ wl_nl :: alt_cont ps cs bs i.

Definition alt_seq (ps cs : list nat) (bs : list (list (bv 8))) (q : nat)
  : list (bv 8) :=
  concat (alt_blk ps cs bs <$> List.seq 0 q).

Lemma alt_seq_0 ps cs bs : alt_seq ps cs bs 0 = [].
Proof. reflexivity. Qed.

Lemma alt_seq_S ps cs bs q :
  alt_seq ps cs bs (S q) = alt_seq ps cs bs q ++ alt_blk ps cs bs q.
Proof.
  rewrite /alt_seq List.seq_S fmap_app concat_app Nat.add_0_l /=.
  by rewrite app_nil_r.
Qed.

(* the block reads the body only through [bs !!! i], so two body lists that
   agree there give the same block *)
Lemma alt_cont_bs ps cs bs bs' i :
  bs !!! i = bs' !!! i -> alt_cont ps cs bs i = alt_cont ps cs bs' i.
Proof. intro H. by rewrite /alt_cont H. Qed.

Lemma alt_blk_bs ps cs bs bs' i :
  bs !!! i = bs' !!! i -> alt_blk ps cs bs i = alt_blk ps cs bs' i.
Proof. intro H. by rewrite /alt_blk H (alt_cont_bs ps cs bs bs' i H). Qed.

(* ---- THE LENGTHS, ONCE ----------------------------------------------- *)
(* A body is a JOIN of its words, and an unguarded [rewrite !length_app]
   unfolds it into the arity of that join -- leaving [lia] with two
   different atoms.  So the two decompositions a consumer needs are proved
   HERE, with the [length_app] instances pinned, and nobody above takes a
   session apart with [length_app] again. *)
Lemma alt_blk_length ps cs bs q :
  length (alt_blk ps cs bs q)
  = (length (bs !!! q) + 1 + length (alt_cont ps cs bs q))%nat.
Proof.
  rewrite /alt_blk (length_app (bs !!! q) (wl_nl :: alt_cont ps cs bs q)).
  cbn [length]. lia.
Qed.

Lemma alt_seq_S_length ps cs bs q :
  length (alt_seq ps cs bs (S q))
  = (length (alt_seq ps cs bs q) + length (bs !!! q) + 1
     + length (alt_cont ps cs bs q))%nat.
Proof.
  rewrite alt_seq_S (length_app (alt_seq ps cs bs q) _) alt_blk_length. lia.
Qed.

(* ---- the two extensionality laws the transcript needs ---- *)

Lemma pro_idx_ext cs1 cs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  forall j, (j <= q)%nat -> pro_idx cs1 j = pro_idx cs2 j.
Proof.
  intros Hj j. induction j as [| j IH]; intros Hjq; [done |].
  rewrite !pro_idx_S IH; [| lia]. by rewrite (Hj j ltac:(lia)).
Qed.

Lemma pro_idx_take cs q i : (i <= q)%nat -> pro_idx (take q cs) i = pro_idx cs i.
Proof.
  intros Hi. apply (pro_idx_ext _ _ q); [| lia].
  intros j Hj. rewrite list_lookup_total_alt lookup_take_lt; [| lia].
  by rewrite -list_lookup_total_alt.
Qed.

(* THE CHOICE BYTE EXTENDS AN OPEN ROUND.  [pro_of] of an unresolved
   resolution ends at a letter boundary, so filing the round's next letter
   appends its bytes -- the first of which is the byte the writer is
   putting out. *)
Lemma pro_of_snoc_head (ps : list nat) (a : nat) (b : bv 8) :
  ~ pro_done ps -> pro_alts !!! a !! 0%nat = Some b ->
  (pro_of ps ++ [b]) `prefix_of` pro_of (ps ++ [a]).
Proof.
  intros Hnd Hb. rewrite (pro_of_open_app ps [a] Hnd) pro_of_singleton.
  apply prefix_app.
  destruct (pro_alts !!! a) as [| z zs] eqn:Hz; [discriminate |].
  cbn in Hb. injection Hb as <-. by eexists.
Qed.

(* ...and dropping SETTLED rounds commutes with filing the open one's. *)
Lemma pro_tail_snoc (ps : list nat) (a : nat) :
  (0 < pro_rounds ps)%nat -> pro_tail (ps ++ [a]) = pro_tail ps ++ [a].
Proof.
  induction ps as [| c ps IH]; cbn [pro_rounds pro_tail app]; [lia |].
  case_decide as Hc; [| done]. intros H. by apply IH.
Qed.

Lemma pro_from_snoc_le (r : nat) (ps : list nat) (a : nat) :
  (r <= pro_rounds ps)%nat -> pro_from r (ps ++ [a]) = pro_from r ps ++ [a].
Proof.
  revert ps. induction r as [| r IH]; intros ps Hr; [done |].
  cbn [pro_from]. rewrite pro_tail_snoc; [| lia].
  apply IH. rewrite pro_rounds_tail. lia.
Qed.

(* THE SAME, FOR A WHOLE BLOCK OF CHOICES: once the first [r] rounds have
   settled, dropping them commutes with filing anything at all. *)
Lemma pro_from_app_le (r : nat) (ps z : list nat) :
  (r <= pro_rounds ps)%nat -> pro_from r (ps ++ z) = pro_from r ps ++ z.
Proof.
  intros Hr. induction z as [| a z IH] using rev_ind.
  - by rewrite !app_nil_r.
  - rewrite app_assoc (pro_from_snoc_le r (ps ++ z) a); last first.
    { rewrite pro_rounds_app. lia. }
    rewrite IH. by rewrite -app_assoc.
Qed.

Lemma pro_from_nil (r : nat) : pro_from r [] = [].
Proof. induction r as [| r IH]; [done |]. by cbn [pro_from pro_tail]. Qed.

(* FILING A LETTER AT AN OPEN ROUND LEAVES NOTHING OVER: the round is
   either still open (a continuing letter) or closed by exactly that
   letter, so the resolution never runs ahead of the wire.  ([pro_tail]
   of an open [ps] is [[]], and appending one entry leaves exactly that.) *)
Lemma pro_tail_open_snoc (ps : list nat) (a : nat) :
  ~ pro_done ps -> pro_tail (ps ++ [a]) = [].
Proof.
  induction ps as [| c ps IH]; intros Hnd.
  - cbn [app pro_tail]. by case_decide.
  - assert (Hc1 : pro_cont c).
    { destruct (decide (pro_cont c)) as [? | Hne]; [done |].
      exfalso. apply Hnd. rewrite /pro_done. by apply Exists_cons; left. }
    cbn [app pro_tail]. rewrite decide_True; [| exact Hc1].
    apply IH. intros H. apply Hnd. rewrite /pro_done Exists_cons. by right.
Qed.

(* AN OPEN PROLOGUE GROWS STRICTLY when a letter is filed -- every letter
   is non-empty, so at least its first byte is new.  This is what makes
   the resolution READABLE OFF THE LENGTH of what was written. *)
Lemma pro_of_open_snoc_lt (ps : list nat) (a : nat) :
  ~ pro_done ps -> (a < length pro_alts)%nat ->
  (length (pro_of ps) < length (pro_of (ps ++ [a])))%nat.
Proof.
  intros Hnd Ha.
  destruct (pro_alts !!! a) as [| c bs] eqn:Hz;
    [ exfalso; exact (pro_alts_nonnil a Ha Hz) |].
  assert (Hb : pro_alts !!! a !! 0%nat = Some c) by (by rewrite Hz).
  pose proof (pro_of_snoc_head ps a c Hnd Hb) as Hpre.
  apply prefix_length in Hpre. rewrite (length_app (pro_of ps) [c]) in Hpre.
  cbn [length] in Hpre. lia.
Qed.

(* ...hence an OPEN prologue determines its resolution: nothing can be
   appended without moving the bytes. *)
Lemma pro_of_open_app_inj (ps z : list nat) :
  ~ pro_done ps -> Forall (fun a => (a < length pro_alts)%nat) z ->
  pro_of (ps ++ z) = pro_of ps -> z = [].
Proof.
  intros Hnd HF Heq. destruct z as [| a z]; [done | exfalso].
  rewrite Forall_cons in HF. destruct HF as [Ha _].
  assert (Hp : pro_of (ps ++ [a]) `prefix_of` pro_of (ps ++ a :: z)).
  { apply pro_of_mono. exists z. by rewrite -app_assoc. }
  apply prefix_length in Hp. rewrite Heq in Hp.
  pose proof (pro_of_open_snoc_lt ps a Hnd Ha). lia.
Qed.

(* ...and a settled extension of an open round is STRICTLY longer *)
Lemma pro_of_open_done_lt (ps ps' : list nat) :
  ~ pro_done ps -> pro_done ps' -> ps `prefix_of` ps' ->
  Forall (fun a => (a < length pro_alts)%nat) ps' ->
  (length (pro_of ps) < length (pro_of ps'))%nat.
Proof.
  intros Hnd Hd [z ->] HF.
  destruct z as [| a z].
  { exfalso. rewrite app_nil_r in Hd. exact (Hnd Hd). }
  apply Forall_app in HF as [_ HF]. rewrite Forall_cons in HF.
  destruct HF as [Ha _].
  pose proof (pro_of_open_snoc_lt ps a Hnd Ha) as Hlt.
  assert (Hp : pro_of (ps ++ [a]) `prefix_of` pro_of (ps ++ a :: z)).
  { apply pro_of_mono. exists z. by rewrite -app_assoc. }
  apply prefix_length in Hp. lia.
Qed.

(* THE BANNER OF THE j-TH FAILED SUB-ROUND.  An OPEN prologue with [j]
   failures behind it is [(banner ++ "init: exec sh failed\n")^j], so the
   banner init files next starts at [pro_round * j] -- the ONE arithmetic
   fact init's restart loop needs, at an arbitrary j and with no
   [vm_compute]. *)
Lemma pro_alts_1 : pro_alts !!! 1%nat = u_execfail.
Proof. reflexivity. Qed.

Lemma pro_alts_3 : pro_alts !!! 3%nat = u_banner.
Proof. reflexivity. Qed.

Lemma pro_fail_0 : pro_fail 0 = [].
Proof. reflexivity. Qed.

Lemma pro_fail_S (j : nat) : pro_fail (S j) = pro_fail j ++ [3%nat; 1%nat].
Proof. rewrite /pro_fail. apply concat_replicate_S. Qed.

Lemma pro_fail_cont (j : nat) : Forall pro_cont (pro_fail j).
Proof.
  induction j as [| j IH]; [constructor |].
  rewrite pro_fail_S Forall_app. split; [exact IH |].
  constructor; [by right | constructor; [by left | constructor]].
Qed.

Lemma pro_fail_bound (j : nat) :
  Forall (fun a => (a < length pro_alts)%nat) (pro_fail j).
Proof.
  eapply Forall_impl; [exact (pro_fail_cont j) |].
  intros a [-> | ->]; rewrite pro_alts_length; lia.
Qed.

Lemma pro_done_cont (g : list nat) : Forall pro_cont g -> ~ pro_done g.
Proof.
  intros HF Hd. rewrite /pro_done Exists_exists in Hd.
  destruct Hd as (a & Ha & Hne). apply Hne.
  exact (proj1 (Forall_forall _ _) HF a Ha).
Qed.

Lemma pro_done_fail (j : nat) : ~ pro_done (pro_fail j).
Proof. exact (pro_done_cont _ (pro_fail_cont j)). Qed.

Lemma pro_of_fail_length (j : nat) :
  length (pro_of (pro_fail j)) = (pro_round * j)%nat.
Proof.
  induction j as [| j IH]; [reflexivity |].
  rewrite pro_fail_S (pro_of_open_app _ _ (pro_done_fail j)) length_app IH.
  assert (H31 : length (pro_of [3%nat; 1%nat]) = pro_round).
  { rewrite /pro_round. vm_compute. reflexivity. }
  rewrite H31. lia.
Qed.

Lemma pro_of_fail_banner (j i : nat) (b : bv 8) :
  u_banner !! i = Some b ->
  pro_of (pro_fail j ++ [3%nat]) !! (pro_round * j + i)%nat = Some b.
Proof.
  intros Hb.
  rewrite (pro_of_open_app _ _ (pro_done_fail j)) pro_of_singleton pro_alts_3.
  rewrite -pro_of_fail_length lookup_app_shift. exact Hb.
Qed.

Lemma pro_idx_app_le (cs z : list nat) (q : nat) :
  (q <= length cs)%nat -> pro_idx (cs ++ z) q = pro_idx cs q.
Proof.
  intros Hq. symmetry. apply (pro_idx_ext cs (cs ++ z) q); [| lia].
  intros j Hj. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Lemma alt_seq_ext ps cs1 cs2 bs q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  alt_seq ps cs1 bs q = alt_seq ps cs2 bs q.
Proof.
  intros Hj. induction q as [| q IH]; [done |].
  rewrite !alt_seq_S IH; [| intros j Hjq; apply Hj; lia].
  rewrite /alt_blk /alt_cont (Hj q ltac:(lia)).
  by rewrite (pro_idx_ext cs1 cs2 (S q) Hj q ltac:(lia)).
Qed.

Lemma alt_seq_bs_ext ps cs bs1 bs2 q :
  (forall j, (j < q)%nat -> bs1 !!! j = bs2 !!! j) ->
  alt_seq ps cs bs1 q = alt_seq ps cs bs2 q.
Proof.
  intros Hj. induction q as [| q IH]; [done |].
  rewrite !alt_seq_S IH; [| intros j Hjq; apply Hj; lia].
  by rewrite (alt_blk_bs ps cs bs1 bs2 q (Hj q ltac:(lia))).
Qed.

Lemma alt_seq_bs_app ps cs bs bs' q :
  (q <= length bs)%nat -> alt_seq ps cs (bs ++ bs') q = alt_seq ps cs bs q.
Proof.
  intro Hq. apply alt_seq_bs_ext. intros j Hj.
  rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

(* ...and the one for the PROLOGUES: only the rounds the first [q] lines
   enter are read, which is what makes a lower bound of [ps] worth its
   transcript. *)
Lemma alt_seq_ps_ext ps1 ps2 cs bs q :
  (forall r, (r <= pro_idx cs q)%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_seq ps1 cs bs q = alt_seq ps2 cs bs q.
Proof.
  induction q as [| q IH]; intros Hr; [done |].
  assert (Hle : (pro_idx cs q <= pro_idx cs (S q))%nat)
    by (apply pro_idx_mono; lia).
  rewrite !alt_seq_S IH; [| intros r Hrq; apply Hr; lia].
  rewrite /alt_blk /alt_cont. case_decide as H3; [| done].
  rewrite (Hr (S (pro_idx cs q))); [done |].
  rewrite (pro_idx_S3 cs q H3). lia.
Qed.

(* ---- 2c.  THE SESSION ---- *)

(* THE EXPECTED SESSION TRANSCRIPT for the era's input [I]: the prologue
   this run opened with, then one block per COMPLETED line, then the echo
   of the line in progress.  It reads the input through the PARSE and never
   through its length, which is what lets each round carry its own words. *)
Definition sess (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  pro_of ps ++ alt_seq ps cs (bodies_of I) (nlines I) ++ rest_of I.

Lemma sess_nil ps cs : sess ps cs [] = pro_of ps.
Proof.
  rewrite /sess rest_of_nil nlines_nil alt_seq_0. by rewrite !app_nil_r.
Qed.

Lemma sess_length ps cs I :
  length (sess ps cs I)
  = (length (pro_of ps) + length (alt_seq ps cs (bodies_of I) (nlines I))
     + length (rest_of I))%nat.
Proof.
  rewrite /sess (length_app (pro_of ps) _)
    (length_app (alt_seq ps cs (bodies_of I) (nlines I)) (rest_of I)). lia.
Qed.

Lemma sess_ps_ext ps1 ps2 cs I :
  (forall r, (r <= pro_idx cs (nlines I))%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  sess ps1 cs I = sess ps2 cs I.
Proof.
  intros Hr. rewrite /sess (Hr 0%nat ltac:(lia)).
  by rewrite (alt_seq_ps_ext ps1 ps2 cs (bodies_of I) (nlines I) Hr).
Qed.

(* THE SESSION GROWS WITH THE INPUT, UNCONDITIONALLY.  A byte that is not a
   newline lengthens the line in progress; the newline closes the body --
   whose RAW bytes are the block's echo half -- and opens the block's
   continuation.  Neither step asks anything of the parse, which is why the
   transcript is monotone in the input at any line, admissible or not. *)
Lemma sess_snoc_other ps cs I b :
  b <> wl_nl -> sess ps cs (I ++ [b]) = sess ps cs I ++ [b].
Proof.
  intro Hb. rewrite /sess (bodies_of_snoc_other I b Hb)
    (nlines_snoc_other I b Hb) (rest_of_snoc_other I b Hb).
  by rewrite !app_assoc.
Qed.

Lemma sess_snoc_nl ps cs I :
  sess ps cs (I ++ [wl_nl])
  = sess ps cs I
    ++ wl_nl :: alt_cont ps cs (bodies_of I ++ [rest_of I]) (nlines I).
Proof.
  assert (Hidx : (bodies_of I ++ [rest_of I]) !!! (nlines I) = rest_of I).
  { rewrite list_lookup_total_alt
      (lookup_app_r (bodies_of I) [rest_of I] (nlines I)
         ltac:(rewrite /nlines; lia)).
    rewrite /nlines Nat.sub_diag. reflexivity. }
  rewrite {1}/sess bodies_of_snoc_nl nlines_snoc_nl rest_of_snoc_nl.
  rewrite alt_seq_S (alt_seq_bs_app ps cs (bodies_of I) [rest_of I] (nlines I)
                       ltac:(rewrite /nlines; lia)).
  rewrite /alt_blk Hidx app_nil_r /sess.
  by rewrite !app_assoc.
Qed.

Lemma sess_step ps cs I b : sess ps cs I `prefix_of` sess ps cs (I ++ [b]).
Proof.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite sess_snoc_nl. by eexists.
  - rewrite (sess_snoc_other ps cs I b Hb). by eexists.
Qed.

Lemma sess_mono ps cs I I' :
  I `prefix_of` I' -> sess ps cs I `prefix_of` sess ps cs I'.
Proof.
  intros [k ->]. induction k as [| b k IH] using rev_ind.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. etrans; [exact IH | apply sess_step].
Qed.

Lemma sess_length_step ps cs I b :
  (length (sess ps cs I) < length (sess ps cs (I ++ [b])))%nat.
Proof.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite sess_snoc_nl (length_app (sess ps cs I) _). cbn [length]. lia.
  - rewrite (sess_snoc_other ps cs I b Hb) (length_app (sess ps cs I) [b]).
    cbn [length]. lia.
Qed.

Lemma sess_length_le ps cs I I' :
  I `prefix_of` I' -> (length (sess ps cs I) <= length (sess ps cs I'))%nat.
Proof. intro Hp. exact (prefix_length _ _ (sess_mono ps cs I I' Hp)). Qed.

Lemma sess_length_lt ps cs I I' :
  I `prefix_of` I' -> I <> I' ->
  (length (sess ps cs I) < length (sess ps cs I'))%nat.
Proof.
  intros [k ->] Hne. destruct k as [| b k _] using rev_ind.
  { exfalso. apply Hne. by rewrite app_nil_r. }
  rewrite app_assoc.
  pose proof (sess_length_le ps cs I (I ++ k) ltac:(by eexists)) as H1.
  pose proof (sess_length_step ps cs (I ++ k) b) as H2. lia.
Qed.

Lemma sess_take ps cs I q :
  (nlines I <= q)%nat -> sess ps (take q cs) I = sess ps cs I.
Proof.
  intros Hq. rewrite /sess. do 2 f_equal.
  apply alt_seq_ext. intros j Hj.
  rewrite list_lookup_total_alt lookup_take_lt; [| lia].
  by rewrite -list_lookup_total_alt.
Qed.

(* EVERY PROLOGUE THE FIRST [q] LINES ENTER HAS SETTLED: round 0, and one
   more for every line that took alternative 3.  This is the side condition
   the DISCIPLINE and the CLAIM carry; the stage machine carries the weaker
   one (every block strictly below the current stage). *)
Definition pro_ok (ps cs : list nat) (q : nat) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps
  /\ (pro_idx cs q < pro_rounds ps)%nat.

Global Instance pro_ok_dec ps cs q : Decision (pro_ok ps cs q).
Proof. rewrite /pro_ok. apply _. Defined.

Lemma pro_ok_mono ps cs q q' : (q' <= q)%nat -> pro_ok ps cs q -> pro_ok ps cs q'.
Proof.
  intros Hq [HF Hlt]. split; [exact HF |].
  pose proof (pro_idx_mono cs q' q Hq). lia.
Qed.

(* dropping rounds composes, and it eats settled rounds one at a time *)
Lemma pro_from_add a b ps : pro_from a (pro_from b ps) = pro_from (b + a) ps.
Proof.
  revert ps. induction b as [| b IH]; intros ps; [done |].
  cbn [pro_from Nat.add]. apply IH.
Qed.

Lemma pro_rounds_from r ps : pro_rounds (pro_from r ps) = (pro_rounds ps - r)%nat.
Proof.
  revert ps. induction r as [| r IH]; intros ps; [cbn; lia |].
  cbn [pro_from]. rewrite IH pro_rounds_tail. lia.
Qed.

Lemma pro_from_Forall (P : nat -> Prop) r ps :
  Forall P ps -> Forall P (pro_from r ps).
Proof.
  revert ps. induction r as [| r IH]; intros ps HF; [exact HF |].
  cbn [pro_from]. by apply IH, pro_tail_Forall.
Qed.

Lemma pro_idx_S_le cs i : (pro_idx cs (S i) <= S (pro_idx cs i))%nat.
Proof. rewrite pro_idx_S. case_decide; lia. Qed.

(* ---- how many rounds the input has STARTED ---- *)

(* [nstarted I] is [nlines I] plus one when a line is in progress: the
   number of rounds the user has begun.  It replaces "the input length
   divided by the line length, rounded up" and is the index the stage's
   side condition quantifies over. *)
Lemma nstarted_snoc_nl I : nstarted (I ++ [wl_nl]) = S (nlines I).
Proof.
  rewrite /nstarted nlines_snoc_nl rest_of_snoc_nl.
  case_decide as H; [lia | by destruct (H eq_refl)].
Qed.

Lemma nstarted_snoc_other I b :
  b <> wl_nl -> nstarted (I ++ [b]) = S (nlines I).
Proof.
  intro Hb. rewrite /nstarted (nlines_snoc_other I b Hb)
    (rest_of_snoc_other I b Hb).
  case_decide as H; [| lia]. exfalso.
  apply (f_equal length) in H.
  rewrite (length_app (rest_of I) [b]) in H. cbn [length] in H. lia.
Qed.

(* a nonempty input has started a round -- and that is what makes the
   stage's side condition say something at the head of the transcript *)
Lemma nstarted_pos I : I <> [] -> (0 < nstarted I)%nat.
Proof.
  intro Hne. rewrite /nstarted. case_decide as H; [| lia].
  destruct (decide (nlines I = 0)%nat) as [Hz | ?]; [| lia].
  exfalso. apply Hne.
  assert (Hb : bodies_of I = []) by (apply nil_length_inv; exact Hz).
  by rewrite (wl_cut_join I) H Hb wl_join_nil app_nil_r.
Qed.

Lemma nlines_le_nstarted I : (nlines I <= nstarted I)%nat.
Proof. rewrite /nstarted. case_decide; lia. Qed.

Lemma nstarted_le_S I : (nstarted I <= S (nlines I))%nat.
Proof. rewrite /nstarted. case_decide; lia. Qed.

Lemma nlines_prefix I I' : I `prefix_of` I' -> (nlines I <= nlines I')%nat.
Proof. intros [k ->]. apply nlines_app_le. Qed.

Lemma nstarted_prefix I I' :
  I `prefix_of` I' -> (nstarted I <= nstarted I')%nat.
Proof.
  intro Hp. pose proof (nlines_prefix I I' Hp) as Hle.
  destruct (decide (nlines I = nlines I')) as [Heq | Hne].
  - pose proof (rest_of_prefix I I' Hp Heq) as Hr.
    rewrite /nstarted. case_decide as H1; case_decide as H2; try lia.
    exfalso. apply H1. rewrite H2 in Hr. by apply prefix_nil_inv in Hr.
  - pose proof (nlines_le_nstarted I') as H2.
    pose proof (nstarted_le_S I) as H1. lia.
Qed.

(* A STRICT PREFIX OF THE INPUT HAS FEWER COMPLETE LINES THAN THE INPUT HAS
   STARTED ROUNDS -- the one step that turns "this stage is not the last"
   into the stage's side condition. *)
Lemma nstarted_strict J I :
  J `prefix_of` I -> J <> I -> (nlines J < nstarted I)%nat.
Proof.
  intros [k Hk] Hne. destruct k as [| b k].
  { exfalso. apply Hne. by rewrite Hk app_nil_r. }
  assert (Hp : J ++ [b] `prefix_of` I) by (exists k; by rewrite Hk -app_assoc).
  pose proof (nstarted_prefix (J ++ [b]) I Hp) as Hle.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite nstarted_snoc_nl in Hle. lia.
  - rewrite (nstarted_snoc_other J b Hb) in Hle. lia.
Qed.

(* THE STAGE'S side condition: every round the input has STARTED reads a
   prologue that has settled.  The round the writer is standing in need not
   have -- it settles at that block's choice byte -- which is exactly the
   difference from [pro_ok]. *)
Definition pro_pin (ps cs : list nat) (I : list (bv 8)) : Prop :=
  forall q, (q < nstarted I)%nat -> (pro_idx cs q < pro_rounds ps)%nat.

Lemma pro_pin_nil ps cs : pro_pin ps cs [].
Proof. intros q Hq. rewrite nstarted_nil in Hq. lia. Qed.

Lemma pro_pin_at ps cs I q :
  pro_pin ps cs I -> (q < nstarted I)%nat ->
  (pro_idx cs q < pro_rounds ps)%nat.
Proof. intros Hp Hq. exact (Hp q Hq). Qed.

Lemma pro_pin_prefix ps cs I I' :
  I `prefix_of` I' -> pro_pin ps cs I' -> pro_pin ps cs I.
Proof.
  intros Hpre Hp q Hq. apply Hp.
  pose proof (nstarted_prefix I I' Hpre). lia.
Qed.

Lemma pro_pin_idx_le ps cs I :
  pro_pin ps cs I -> (pro_idx cs (nlines I) <= pro_rounds ps)%nat.
Proof.
  intros Hp. pose proof (nlines_le_nstarted I) as Hn.
  destruct (decide (nlines I < nstarted I)%nat) as [Hlt | Hge].
  - pose proof (Hp (nlines I) Hlt). lia.
  - destruct (nlines I) as [| m] eqn:Hm; [cbn [pro_idx]; lia |].
    assert (Hlt' : (m < nstarted I)%nat) by lia.
    pose proof (Hp m Hlt'). pose proof (pro_idx_S_le cs m). lia.
Qed.

Lemma pro_pin_mono ps ps' cs I :
  ps `prefix_of` ps' -> pro_pin ps cs I -> pro_pin ps' cs I.
Proof.
  intros [z ->] Hp q Hq. pose proof (Hp q Hq).
  rewrite pro_rounds_app. lia.
Qed.

(* the bridge [good_out_of_stage] spends: PADDING the resolution with
   terminated rounds turns the stage's condition into the claim's, at any
   line count the padding covers.  It moves no round the stage has read
   ([pro_of_from_done_ext]). *)
Lemma pro_ok_pad ps cs m d :
  Forall (fun x => (x < length pro_alts)%nat) ps -> (m <= d)%nat ->
  pro_ok (ps ++ replicate (S d) 0%nat) cs m.
Proof.
  intros HF Hm. split.
  - apply Forall_app. split; [exact HF |].
    apply Forall_forall. intros x Hx. apply elem_of_replicate in Hx as [-> _].
    rewrite pro_alts_length. lia.
  - rewrite pro_rounds_app pro_rounds_replicate_0.
    pose proof (pro_idx_le cs m). lia.
Qed.

(* the bridge [good_out_of_stage] spends: PADDING the resolution with one
   terminated round turns the stage's condition into the claim's. *)
Lemma pro_pin_ok ps cs I a :
  pro_pin ps cs I -> Forall (fun x => (x < length pro_alts)%nat) ps ->
  ~ pro_cont a -> (a < length pro_alts)%nat ->
  pro_ok (ps ++ [a]) cs (nlines I).
Proof.
  intros Hp HF Hne Ha. split.
  - apply Forall_app. split; [exact HF | by apply Forall_singleton].
  - rewrite pro_rounds_app.
    pose proof (pro_pin_idx_le ps cs I Hp).
    assert (Hr : pro_rounds [a] = 1%nat).
    { cbn [pro_rounds]. rewrite decide_False; [lia | exact Hne]. }
    lia.
Qed.

(* R3's relation: [out] is what the session may have emitted for input [I],
   under SOME resolution of the prologue's and the per-line alternatives. *)
Definition expected_rel (I out : list (bv 8)) : Prop :=
  exists ps cs : list nat,
    pro_ok ps cs (nlines I)
    /\ Forall (fun c => (c < 4)%nat) cs
    /\ out `prefix_of` sess ps cs I.

Lemma expected_rel_out_mono I out out' :
  out' `prefix_of` out -> expected_rel I out -> expected_rel I out'.
Proof.
  intros Hp (ps & cs & Hok & Hcs & Hout). exists ps, cs.
  split; [exact Hok|]. split; [exact Hcs|]. by etrans.
Qed.

(* R3's monotonicity in the INPUT.  The resolution has to be PADDED: a
   longer input may complete more lines, each of which may be a shell that
   died on its own fork panic and re-entered the prologue, so [pro_ok] at
   the longer input asks for more settled rounds than the shorter one
   supplies.  Padding with terminated rounds changes no round the shorter
   transcript reads ([pro_of_from_done_ext]). *)
Lemma expected_rel_ins_prefix I I' out :
  I `prefix_of` I' -> expected_rel I out -> expected_rel I' out.
Proof.
  intros Hpre (ps & cs & [HF Hlt] & Hcs & Hout).
  set (pad := replicate (S (nlines I')) 0%nat).
  exists (ps ++ pad), cs. split.
  { split.
    - apply Forall_app. split; [exact HF |].
      apply Forall_forall. intros x Hx. apply elem_of_replicate in Hx as [-> _].
      rewrite pro_alts_length. lia.
    - rewrite pro_rounds_app /pad pro_rounds_replicate_0.
      pose proof (pro_idx_le cs (nlines I')). lia. }
  split; [exact Hcs |].
  etrans; [exact Hout |].
  rewrite (sess_ps_ext ps (ps ++ pad) cs I); last first.
  { intros r Hr.
    apply (pro_of_from_done_ext r ps (ps ++ pad)); [by eexists | lia]. }
  by apply sess_mono.
Qed.

Lemma prefix_take_le {A} (l : list A) (n m : nat) :
  n <= m -> take n l `prefix_of` take m l.
Proof.
  intros Hnm.
  assert (H : take n l = take n (take m l)).
  { rewrite take_take Nat.min_l; [done|lia]. }
  rewrite H. apply prefix_take.
Qed.

(* ====================================================================== *)
(*  3.  THE WIRE THE USER HAD SEEN AT EACH INPUT                           *)
(* ====================================================================== *)

(* the wire the user had seen when each input byte was typed: [in_pres seg]
   lists, in order, the prefix of [seg] STRICTLY BEFORE its i-th
   [ObsUartIn Uart0]. *)
Fixpoint in_pres (seg : list mobs) : list (list mobs) :=
  match seg with
  | [] => []
  | ObsUartIn Uart0 b :: seg' => [] :: ((fun p => ObsUartIn Uart0 b :: p) <$> in_pres seg')
  | e :: seg' => (fun p => e :: p) <$> in_pres seg'
  end.

Lemma in_pres_length seg : length (in_pres seg) = length (ins seg).
Proof.
  induction seg as [|e seg IH]; [done|].
  destruct e as [[] ?|[] ?| |]; cbn; rewrite ?length_fmap IH //.
Qed.

(* AN EVENT THAT IS NOT A CONSOLE INPUT IS INVISIBLE TO THE DISCIPLINE.
   The machine has two 16550s and the discipline reads ONE of them -- the
   console's input side and the console's wire -- so an output byte, and
   ANY event of the other port, leaves both [ins] and [in_pres] alone. *)
Definition not_cons_in (e : mobs) : Prop :=
  match e with ObsUartIn Uart0 _ => False | _ => True end.

Lemma ins_snoc_other e : not_cons_in e -> ins [e] = [].
Proof. destruct e as [[] ?|[] ?| |]; cbn; done. Qed.

Lemma in_pres_snoc_other seg e :
  not_cons_in e -> in_pres (seg ++ [e]) = in_pres seg.
Proof.
  intro He. induction seg as [|x seg IH].
  - destruct e as [[] ?|[] ?| |]; cbn in He |- *; done.
  - destruct x as [[] ?|[] ?| |]; cbn; rewrite IH //.
Qed.

Lemma in_pres_out seg i b : in_pres (seg ++ [ObsUartOut i b]) = in_pres seg.
Proof. apply in_pres_snoc_other. by destruct i. Qed.

Lemma in_pres_in seg b : in_pres (seg ++ [ObsUartIn Uart0 b]) = in_pres seg ++ [seg].
Proof.
  induction seg as [|e seg IH]; [done|].
  destruct e as [[] ?|[] ?| |]; cbn; rewrite IH ?fmap_app //.
Qed.

(* ====================================================================== *)
(*  4.  THE DISCIPLINE (R4)                                               *)
(* ====================================================================== *)

(* D1 AT ONE INPUT POSITION.  [p] is the wire before an input byte: the
   expected transcript for the input's COMPLETE LINES is already there.  At
   a line boundary that transcript ends in the "$ " of the previous line's
   continuation, and at the empty input it is init's banner and sh's first
   prompt; MID-LINE it is the very same transcript, because [done_of] drops
   the line in progress -- which is what lets the whole line be typed as a
   burst.

   The wire is the CONSOLE's, and nothing but the session writes it, so the
   transcript is measured from the start of the wire: there is no kernel
   prefix to skip and no partial prologue to name.  WHAT THIS DOES AND DOES
   NOT CLAIM, as fact: a user who types the first byte of a line before the
   previous line's block has ended in "$ " is outside the discipline, and
   the theorem says nothing about that cycle beyond safety. *)
Definition disc_pt (ps cs : list nat) (p : list mobs) : Prop :=
  sess ps cs (done_of (ins p)) `prefix_of` obs_wire Uart0 p.

Global Instance disc_pt_dec ps cs p : Decision (disc_pt ps cs p).
Proof. rewrite /disc_pt. apply _. Defined.

(* THE STRICT RULE IMPLIES THE RELAXED ONE.  A session that waited for
   every byte's echo is disciplined here too ([sess_mono] at
   [LineWords.done_of_prefix]) -- which is what carries a witness, or a
   sibling application's stricter per-position rule, into this one. *)
Lemma disc_pt_of_strict (ps cs : list nat) (p : list mobs) :
  sess ps cs (ins p) `prefix_of` obs_wire Uart0 p -> disc_pt ps cs p.
Proof.
  intro H. rewrite /disc_pt. etrans; [| exact H].
  apply sess_mono, done_of_prefix.
Qed.

(* THE PER-CYCLE DISCIPLINE: D3, and at every input byte D1 under ONE
   resolution of the prologue's and the per-line alternatives.  [pro_ok] is
   stated AT THE INPUT and not once for the segment, because that is where
   it is true: it says every prologue the transcript for THAT input enters
   has settled, and a segment the user never typed into enters none (and
   must stay disciplined -- [disc_seg'_nil]). *)
Definition disc_seg' (seg : list mobs) : Prop :=
  disc_seg seg
  /\ exists ps cs : list nat,
       length cs = nlines (ins seg)
       /\ Forall (fun c => (c < 4)%nat) cs
       /\ forall p : list mobs, p ∈ in_pres seg ->
            pro_ok ps cs (nlines (ins p)) /\ disc_pt ps cs p.

(* ---- decidability: the choice list is bounded, so the search is finite ---- *)

Fixpoint bounded_lists (k n : nat) : list (list nat) :=
  match n with
  | O => [[]]
  | S n' => (fun p => p.1 :: p.2) <$>
              (List.list_prod (List.seq 0 k) (bounded_lists k n'))
  end.

Lemma elem_of_bounded_lists (k n : nat) (cs : list nat) :
  cs ∈ bounded_lists k n <-> length cs = n /\ Forall (fun c => c < k) cs.
Proof.
  revert cs. induction n as [|n IH]; intros cs; cbn.
  - rewrite list_elem_of_singleton. split.
    + intros ->. split; [done|constructor].
    + intros [Hl _]. by apply nil_length_inv.
  - rewrite list_elem_of_fmap. split.
    + intros ([c cs'] & -> & Hp). cbn.
      apply list_elem_of_In in Hp. apply in_prod_iff in Hp as [Hc Hcs].
      apply in_seq in Hc. apply list_elem_of_In in Hcs.
      apply IH in Hcs as [Hl Hf].
      split; [by rewrite /= Hl|]. rewrite Forall_cons. split; [lia|exact Hf].
    + intros [Hl Hf]. destruct cs as [|c cs']; [done|].
      rewrite Forall_cons in Hf. destruct Hf as [Hc Hf].
      exists (c, cs'). split; [done|].
      apply list_elem_of_In, in_prod_iff. split.
      * apply in_seq. lia.
      * apply list_elem_of_In, IH. split; [by injection Hl|exact Hf].
Qed.

Lemma Forall_imap_pair {A} (P : nat -> A -> Prop) (l : list A) :
  Forall (fun ip => P ip.1 ip.2) (imap (fun i x => (i, x)) l)
  <-> forall i x, l !! i = Some x -> P i x.
Proof.
  rewrite Forall_lookup. split.
  - intros HF i x Hx. apply (HF i (i, x)). by rewrite list_lookup_imap Hx.
  - intros HF i [j x] Hj. rewrite list_lookup_imap in Hj.
    destruct (l !! i) as [y|] eqn:E; [|done]. cbn in Hj. simplify_eq.
    by apply HF.
Qed.

(* ---- the PROLOGUE candidates: the CANONICAL resolutions ----
   [bounded_lists 4 L] would be 4^L and would put the literals below out of
   [vm_compute]'s reach.  A settled round IS its letters -- the continuing
   ones, then one ending letter -- and every letter costs at least two wire
   bytes, so both the number of rounds and each round's length are bounded
   by the segment ([pro_canon], [sess_pro_len]), and the search is
   finite. *)
Fixpoint cont_lists (n : nat) : list (list nat) :=
  match n with
  | O => [[]]
  | S n' => (fun p => p.1 :: p.2) <$>
              (List.list_prod [1%nat; 3%nat] (cont_lists n'))
  end.

Lemma elem_of_cont_lists (n : nat) (g : list nat) :
  g ∈ cont_lists n <-> length g = n /\ Forall pro_cont g.
Proof.
  revert g. induction n as [|n IH]; intros g; cbn [cont_lists].
  - rewrite list_elem_of_singleton. split.
    + intros ->. split; [done|constructor].
    + intros [Hl _]. by apply nil_length_inv.
  - rewrite list_elem_of_fmap. split.
    + intros ([c g'] & -> & Hp). cbn.
      apply list_elem_of_In in Hp. apply in_prod_iff in Hp as [Hc Hg].
      apply list_elem_of_In in Hg. apply IH in Hg as [Hl Hf].
      split; [by rewrite /= Hl|]. rewrite Forall_cons. split; [| exact Hf].
      apply list_elem_of_In in Hc. rewrite /pro_cont.
      apply elem_of_cons in Hc as [-> | Hc]; [by left |].
      apply list_elem_of_singleton in Hc. by right.
    + intros [Hl Hf]. destruct g as [|c g']; [done|].
      rewrite Forall_cons in Hf. destruct Hf as [Hc Hf].
      exists (c, g'). split; [done|].
      apply list_elem_of_In, in_prod_iff. split.
      * apply list_elem_of_In. destruct Hc as [-> | ->];
          [apply list_elem_of_here | by apply list_elem_of_further, list_elem_of_here].
      * apply list_elem_of_In, IH. split; [by injection Hl|exact Hf].
Qed.

Definition pro_grp_cands (m : nat) : list (list nat) :=
  mjoin ((fun k => mjoin ((fun g => [g ++ [0%nat]; g ++ [2%nat]])
                          <$> cont_lists k)) <$> List.seq 0 (S m)).

Fixpoint pro_cands (rounds m : nat) : list (list nat) :=
  match rounds with
  | 0%nat => [[]]
  | S r => (fun q => q.1 ++ q.2) <$>
             List.list_prod (pro_grp_cands m) (pro_cands r m)
  end.

Lemma elem_of_pro_grp_cands (m : nat) (g : list nat) (t : nat) :
  Forall pro_cont g -> (length g <= m)%nat -> (t = 0%nat \/ t = 2%nat) ->
  (g ++ [t]) ∈ pro_grp_cands m.
Proof.
  intros Hg Hk Ht. rewrite /pro_grp_cands list_elem_of_join.
  exists (mjoin ((fun g => [g ++ [0%nat]; g ++ [2%nat]]) <$> cont_lists (length g))).
  split.
  - rewrite list_elem_of_join. exists [g ++ [0%nat]; g ++ [2%nat]]. split.
    + destruct Ht as [-> | ->];
        [ apply list_elem_of_here | by apply list_elem_of_further, list_elem_of_here ].
    + apply list_elem_of_fmap. exists g. split; [reflexivity |].
      apply elem_of_cont_lists. by split.
  - apply list_elem_of_fmap. exists (length g). split; [reflexivity |].
    apply list_elem_of_In, in_seq. lia.
Qed.

Lemma elem_of_pro_cands_app (R m : nat) (g rest : list nat) :
  g ∈ pro_grp_cands m -> rest ∈ pro_cands R m -> (g ++ rest) ∈ pro_cands (S R) m.
Proof.
  intros Hg Hr. cbn [pro_cands]. apply list_elem_of_fmap.
  exists (g, rest). split; [reflexivity |].
  apply list_elem_of_In, in_prod; by apply list_elem_of_In.
Qed.

Lemma pro_cont_bound (a : nat) : pro_cont a -> (a < length pro_alts)%nat.
Proof. intros [-> | ->]; rewrite pro_alts_length; lia. Qed.

Lemma pro_grp_cands_Forall m g :
  g ∈ pro_grp_cands m -> Forall (fun a => (a < length pro_alts)%nat) g.
Proof.
  rewrite /pro_grp_cands list_elem_of_join. intros (l & Hg & Hl).
  apply list_elem_of_fmap in Hl as (k & -> & _).
  rewrite list_elem_of_join in Hg. destruct Hg as (l2 & Hg & Hl2).
  apply list_elem_of_fmap in Hl2 as (g0 & -> & Hg0).
  apply elem_of_cont_lists in Hg0 as [_ Hc].
  assert (Hrep : Forall (fun a => (a < length pro_alts)%nat) g0).
  { eapply Forall_impl; [exact Hc |]. exact pro_cont_bound. }
  apply elem_of_cons in Hg as [-> | Hg];
    [| apply list_elem_of_singleton in Hg; rewrite Hg];
    (apply Forall_app; split; [exact Hrep |];
     apply Forall_singleton; rewrite pro_alts_length; lia).
Qed.

Lemma pro_cands_Forall R m g :
  g ∈ pro_cands R m -> Forall (fun a => (a < length pro_alts)%nat) g.
Proof.
  revert g. induction R as [| R IH]; intros g Hg; cbn [pro_cands] in Hg.
  - apply list_elem_of_singleton in Hg as ->. constructor.
  - apply list_elem_of_fmap in Hg as ([g1 g2] & -> & Hp). cbn.
    apply list_elem_of_In, in_prod_iff in Hp as [H1 H2].
    apply Forall_app. split.
    + by apply (pro_grp_cands_Forall m), list_elem_of_In.
    + by apply IH, list_elem_of_In.
Qed.

Lemma pro_cands_nonempty (R m : nat) : exists g, g ∈ pro_cands R m.
Proof.
  induction R as [| R IH]; [exists []; by apply list_elem_of_singleton |].
  destruct IH as [g Hg]. exists (([] ++ [0%nat]) ++ g).
  apply elem_of_pro_cands_app; [| exact Hg].
  apply elem_of_pro_grp_cands; [constructor | cbn; lia | by left].
Qed.

(* ---- the canonical form of one round, and of a whole resolution ---- *)

(* a settled resolution starts with a round: continuing letters, then an
   ending one, then the rest *)
Lemma pro_of_first_group (ps : list nat) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> pro_done ps ->
  exists (g : list nat) (t : nat) (z : list nat),
    ps = g ++ [t] ++ z /\ Forall pro_cont g /\ (t = 0%nat \/ t = 2%nat)
    /\ (length g <= length (pro_of ps))%nat.
Proof.
  induction ps as [| a ps IH]; intros HF Hd.
  { by apply Exists_nil in Hd. }
  rewrite Forall_cons in HF. destruct HF as [Ha HF].
  rewrite /pro_done Exists_cons in Hd.
  destruct (decide (pro_cont a)) as [Hc | Hne].
  - destruct Hd as [Hn | Hd]; [done |].
    destruct (IH HF Hd) as (g & t & z & Heq & Hg & Ht & Hk).
    exists (a :: g), t, z. split; [by rewrite Heq |]. split; [by constructor |].
    split; [exact Ht |].
    cbn [pro_of length]. rewrite (pro_more_cont a _ Hc) length_app.
    destruct (pro_alts !!! a) as [| y ys] eqn:Hy;
      [ exfalso; exact (pro_alts_nonnil a Ha Hy) | cbn [length]; lia ].
  - exists [], a, ps. split; [reflexivity |]. split; [constructor |].
    split; [| cbn; lia].
    rewrite pro_alts_length in Ha. rewrite /pro_cont in Hne.
    destruct a as [|[|[|[|a]]]]; [by left | exfalso; apply Hne; by left
                                 | by right | exfalso; apply Hne; by right | lia].
Qed.

Lemma pro_tail_group (g : list nat) (t : nat) (z : list nat) :
  Forall pro_cont g -> ~ pro_cont t -> pro_tail (g ++ [t] ++ z) = z.
Proof.
  intros Hg Ht. induction g as [| a g IH]; cbn [app pro_tail].
  - by rewrite decide_False.
  - rewrite Forall_cons in Hg. destruct Hg as [Ha Hg].
    rewrite decide_True; [| exact Ha]. by apply IH.
Qed.

Lemma pro_of_group_app (g : list nat) (t : nat) (z : list nat) :
  Forall pro_cont g -> ~ pro_cont t ->
  pro_of (g ++ [t] ++ z) = pro_of (g ++ [t]).
Proof.
  intros Hg Ht. induction g as [| a g IH]; cbn [app pro_of].
  - by rewrite !(pro_more_ne t _ Ht).
  - rewrite Forall_cons in Hg. destruct Hg as [Ha Hg].
    by rewrite !(pro_more_cont a _ Ha) IH.
Qed.

Lemma pro_canon (R m : nat) : forall ps : list nat,
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  (forall r, (r < R)%nat -> (r < pro_rounds ps)%nat
             /\ (length (pro_of (pro_from r ps)) <= m)%nat) ->
  exists ps0, ps0 ∈ pro_cands R m
    /\ pro_rounds ps0 = R
    /\ (forall r, (r < R)%nat -> pro_of (pro_from r ps0) = pro_of (pro_from r ps)).
Proof.
  induction R as [| R IH]; intros ps HF Hb.
  { exists []. split; [by apply list_elem_of_singleton |].
    split; [reflexivity |]. intros r Hr. lia. }
  destruct (Hb 0%nat ltac:(lia)) as [Hr0 Hm0]. cbn [pro_from] in Hm0.
  assert (Hd : pro_done ps) by (apply (pro_from_done 0%nat ps); exact Hr0).
  destruct (pro_of_first_group ps HF Hd) as (g & t & z & Heq & Hg & Ht & Hk).
  assert (Htne : ~ pro_cont t) by (destruct Ht as [-> | ->]; intros [H | H]; lia).
  destruct (IH (pro_tail ps) (pro_tail_Forall _ _ HF))
    as (ps1 & Hin1 & Hrd1 & Hag1).
  { intros r Hr. destruct (Hb (S r) ltac:(lia)) as [H1 H2].
    cbn [pro_from] in H2. rewrite pro_rounds_tail. split; [lia | exact H2]. }
  exists ((g ++ [t]) ++ ps1). split.
  { apply elem_of_pro_cands_app; [| exact Hin1].
    apply elem_of_pro_grp_cands; [exact Hg | lia | exact Ht]. }
  split.
  { rewrite -app_assoc pro_rounds_group; [by rewrite Hrd1 | exact Hg | exact Htne]. }
  intros r Hr. destruct r as [| r].
  - cbn [pro_from]. rewrite -app_assoc (pro_of_group_app g t ps1 Hg Htne).
    rewrite Heq (pro_of_group_app g t z Hg Htne). reflexivity.
  - cbn [pro_from]. rewrite -app_assoc (pro_tail_group g t ps1 Hg Htne).
    apply Hag1. lia.
Qed.

(* ---- the bound the discipline itself supplies ---- *)

Lemma in_pres_prefix_all (seg : list mobs) :
  Forall (fun p => p `prefix_of` seg) (in_pres seg).
Proof.
  induction seg as [| e seg IH]; [constructor |].
  destruct e as [[] c | [] c | |]; cbn [in_pres];
    try (apply Forall_fmap; eapply Forall_impl; [exact IH |];
         intros q Hq; rewrite /compose; by apply prefix_cons).
  constructor; [apply prefix_nil |].
  apply Forall_fmap. eapply Forall_impl; [exact IH |].
  intros q Hq. rewrite /compose. by apply prefix_cons.
Qed.

Lemma in_pres_prefix (seg : list mobs) (i : nat) (p : list mobs) :
  in_pres seg !! i = Some p -> p `prefix_of` seg.
Proof. intros Hi. exact (Forall_lookup_1 _ _ _ _ (in_pres_prefix_all seg) Hi). Qed.

Lemma obs_wire_length (i : uart_id) (s : list mobs) :
  (length (obs_wire i s) <= length s)%nat.
Proof.
  induction s as [| e s IH]; [done |].
  destruct e as [j b | j b | |]; cbn [obs_wire length];
    repeat case_decide; cbn [length]; lia.
Qed.

(* EVERY ROUND THE TRANSCRIPT ENTERS IS ON THE WIRE, so the search space is
   bounded by the segment. *)
Lemma alt_seq_pro_len ps cs bs q r :
  (r <= pro_idx cs q)%nat ->
  (length (pro_of (pro_from r ps))
   <= length (pro_of ps) + length (alt_seq ps cs bs q))%nat.
Proof.
  revert r. induction q as [| q IH]; intros r Hr.
  - assert (r = 0%nat) by (cbn in Hr; lia). subst r. cbn [pro_from]. lia.
  - rewrite alt_seq_S_length.
    destruct (decide (r <= pro_idx cs q)%nat) as [Hle | Hgt].
    + pose proof (IH r Hle). lia.
    + assert (H3 : cs !!! q = 3%nat).
      { destruct (decide (cs !!! q = 3%nat)) as [? | Hn]; [done |].
        exfalso. rewrite (pro_idx_Sne cs q Hn) in Hr. lia. }
      rewrite (pro_idx_S3 cs q H3) in Hr.
      assert (Hre : r = S (pro_idx cs q)) by lia.
      rewrite /alt_cont (length_app (line_alts_of _ !!! _) _) decide_True;
        [| exact H3].
      rewrite Hre. lia.
Qed.

Lemma sess_pro_len ps cs I r :
  (r <= pro_idx cs (nlines I))%nat ->
  (length (pro_of (pro_from r ps)) <= length (sess ps cs I))%nat.
Proof.
  intros Hr. rewrite sess_length.
  pose proof (alt_seq_pro_len ps cs (bodies_of I) (nlines I) r Hr). lia.
Qed.

(* ...and the ROUND COUNT is bounded by the deepest input point, which is
   what makes the prologue search finite.  [in_pres] is a list, so the
   deepest point is a maximum over it and is attained. *)
Fixpoint nlines_max (l : list (list mobs)) : nat :=
  match l with
  | [] => 0%nat
  | p :: r => Nat.max (nlines (ins p)) (nlines_max r)
  end.

(* the cons step, named once: [cbn] would also take the tail apart and
   leave [lia] with two atoms where the hypotheses name one *)
Lemma nlines_max_cons (p : list mobs) (l : list (list mobs)) :
  nlines_max (p :: l) = Nat.max (nlines (ins p)) (nlines_max l).
Proof. reflexivity. Qed.

Lemma nlines_max_ge (l : list (list mobs)) (p : list mobs) :
  p ∈ l -> (nlines (ins p) <= nlines_max l)%nat.
Proof.
  induction l as [| q l IH]; intro Hp; [by apply elem_of_nil in Hp |].
  rewrite nlines_max_cons.
  apply elem_of_cons in Hp as [-> | Hp]; [lia |].
  pose proof (IH Hp). lia.
Qed.

Lemma nlines_max_mem (l : list (list mobs)) :
  l <> [] -> exists p, p ∈ l /\ nlines (ins p) = nlines_max l.
Proof.
  induction l as [| q l IH]; intro Hne; [done |].
  rewrite nlines_max_cons. destruct l as [| q1 l1].
  { exists q. split; [apply list_elem_of_here |]. cbn [nlines_max]. lia. }
  destruct (IH ltac:(discriminate)) as (p & Hp & Hpe).
  destruct (decide (nlines (ins q) <= nlines_max (q1 :: l1))%nat) as [Hle | Hgt].
  - exists p. split; [by apply list_elem_of_further | lia].
  - exists q. split; [apply list_elem_of_here | lia].
Qed.

(* ---- the constructor the literals below spend ---- *)

Definition disc_pt_all (ps cs : list nat) (seg : list mobs) : Prop :=
  Forall (fun p => pro_ok ps cs (nlines (ins p)) /\ disc_pt ps cs p)
    (in_pres seg).

Global Instance disc_pt_all_dec ps cs seg : Decision (disc_pt_all ps cs seg).
Proof. rewrite /disc_pt_all. apply _. Defined.

Lemma disc_seg'_intro (seg : list mobs) (ps cs : list nat) :
  disc_seg seg ->
  length cs = nlines (ins seg) ->
  Forall (fun c => (c < 4)%nat) cs ->
  disc_pt_all ps cs seg ->
  disc_seg' seg.
Proof.
  intros Hd Hl Hf Hall. split; [exact Hd |]. exists ps, cs.
  split; [exact Hl |]. split; [exact Hf |].
  intros p Hp. exact (proj1 (Forall_forall _ _) Hall p Hp).
Qed.

(* the intro direction at an EXPLICIT predicate: [apply]'s higher-order
   unification cannot guess [P] out of a conjunction. *)
Lemma Forall_imap_pair_intro {A} (P : nat -> A -> Prop) (l : list A) :
  (forall i x, l !! i = Some x -> P i x) ->
  Forall (fun ip => P ip.1 ip.2) (imap (fun i x => (i, x)) l).
Proof. apply Forall_imap_pair. Qed.

Global Instance disc_seg'_dec seg : Decision (disc_seg' seg).
Proof.
  destruct (decide (disc_seg seg)) as [Hd | Hd]; [| right; by intros [? _]].
  destruct (decide (Exists (fun cs =>
                      Exists (fun ps => disc_pt_all ps cs seg)
                        (pro_cands
                           (S (pro_idx cs (nlines_max (in_pres seg))))
                           (length seg)))
                    (bounded_lists 4 (nlines (ins seg))))) as [HE | HE].
  - left. apply Exists_exists in HE as (cs & Hcs & HP).
    apply Exists_exists in HP as (ps & _ & Hall).
    apply elem_of_bounded_lists in Hcs as [Hl Hf].
    by eapply disc_seg'_intro.
  - right. intros [_ (ps & cs & Hl & Hf & Hall)]. apply HE.
    apply Exists_exists. exists cs. split; [by apply elem_of_bounded_lists |].
    apply Exists_exists.
    destruct (decide (in_pres seg = [])) as [Hz | Hz].
    { (* no input at all: the clause is vacuous and any candidate serves *)
      destruct (pro_cands_nonempty
                  (S (pro_idx cs (nlines_max (in_pres seg)))) (length seg))
        as [g Hg].
      exists g. split; [exact Hg |]. rewrite /disc_pt_all Hz. constructor. }
    (* the DEEPEST input point bounds every round the transcript enters *)
    destruct (nlines_max_mem (in_pres seg) Hz) as (pl & Hplin & Hpleq).
    destruct (Hall pl Hplin) as [[HFps Hltl] Hptl].
    assert (Hplp : pl `prefix_of` seg)
      by (exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) pl Hplin)).
    destruct (pro_canon (S (pro_idx cs (nlines_max (in_pres seg))))
                (length seg) ps HFps) as (ps0 & Hin0 & Hrd0 & Hag0).
    { intros r Hr. rewrite -Hpleq in Hr. split; [lia |].
      etrans; [apply (sess_pro_len ps cs (done_of (ins pl)) r);
               rewrite nlines_done; lia |].
      etrans; [apply prefix_length, Hptl |].
      etrans; [apply obs_wire_length |].
      exact (prefix_length _ _ Hplp). }
    exists ps0. split; [exact Hin0 |].
    rewrite /disc_pt_all. apply Forall_forall. intros p Hp.
    destruct (Hall p Hp) as [[_ Hltp] Hptp].
    assert (Hidxle : (pro_idx cs (nlines (ins p))
                      <= pro_idx cs (nlines_max (in_pres seg)))%nat)
      by (apply pro_idx_mono, nlines_max_ge, Hp).
    assert (Hsame : sess ps0 cs (done_of (ins p)) = sess ps cs (done_of (ins p))).
    { apply sess_ps_ext. intros r Hr. rewrite nlines_done in Hr.
      apply Hag0. lia. }
    split.
    + rewrite /pro_ok. split; [by eapply pro_cands_Forall | lia].
    + rewrite /disc_pt Hsame. exact Hptp.
Defined.

Lemma disc_seg'_nil : disc_seg' [].
Proof.
  split; [exact disc_seg_nil |]. exists [], [].
  split; [change (ins []) with (@nil (bv 8)); rewrite nlines_nil; reflexivity |].
  split; [constructor |]. intros p Hp. by apply elem_of_nil in Hp.
Qed.

(* THE PROJECTION.  Everything the tree proves against the content half
   reads off the whole discipline in one step. *)
Lemma disc_seg'_proj seg : disc_seg' seg -> disc_seg seg.
Proof. by intros [? _]. Qed.

(* ANTI-VACUITY AT A LITERAL.  [disc_seg'] is not merely decidable and
   prefix-closed: it is SATISFIED, and by a session in which EACH ROUND
   TYPES ITS OWN LINE -- [echo hi], answered by [hi], then [echo bye now],
   answered by [bye now].  A one-line witness would leave the whole point
   of the model untested, because one line is also what a session with the
   line hard-coded does.  Everything in it is closed, so [vm_compute]
   answers it through the parser, and it is the check that says D1 and
   the per-round parse did not make the discipline unsatisfiable. *)
Definition demo_ws1 : list (list (bv 8)) := [sb "echo"%string; sb "hi"%string].
Definition demo_ws2 : list (list (bv 8)) :=
  [sb "echo"%string; sb "bye"%string; sb "now"%string].

Definition demo_out (l : list (bv 8)) : list mobs :=
  (fun b => ObsUartOut Uart0 b) <$> l.

Definition demo_typed (l : list (bv 8)) : list mobs :=
  mjoin ((fun b => [ObsUartIn Uart0 b; ObsUartOut Uart0 b]) <$> l).

Definition demo_in (l : list (bv 8)) : list mobs :=
  (fun b => ObsUartIn Uart0 b) <$> l.

Definition demo_seg2 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (wl_line demo_ws1)
  ++ demo_out (line_alts_of demo_ws1 !!! 0%nat)
  ++ demo_typed (wl_line demo_ws2)
  ++ demo_out (line_alts_of demo_ws2 !!! 0%nat).

Lemma demo_disc_seg'2 : disc_seg' demo_seg2.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 0%nat] [0%nat; 0%nat]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* ...AND AT THE FOUR OTHER OPENINGS.  These are the literals that say the
   owner's rulings of 2026-09-16 and 2026-09-14 did not make the discipline
   vacuous: the shell that had to be started twice, the fork that failed,
   the shell that died on its own fork panic after a completed line, and
   the shell whose init printed no banner at all. *)
Definition demo_seg_exec : list mobs :=
  demo_out (pro_of [3%nat; 1%nat; 3%nat; 0%nat])
  ++ [ObsUartIn Uart0 (Z_to_bv 8 101%Z)].

Lemma demo_disc_seg'_exec : disc_seg' demo_seg_exec.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 1%nat; 3%nat; 0%nat] []);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

Definition demo_seg_fork : list mobs :=
  demo_out (pro_of [3%nat; 2%nat]) ++ [ObsUartIn Uart0 (Z_to_bv 8 101%Z)].

Lemma demo_disc_seg'_fork : disc_seg' demo_seg_fork.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 2%nat] []);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* one whole line typed and echoed, the shell's fork1 panic, and init's
   restart -- the block whose alternative is 3 re-enters the prologue *)
Definition demo_seg_panic : list mobs :=
  demo_out (pro_of [3%nat; 0%nat])
  ++ demo_typed (wl_line demo_ws1)
  ++ demo_out (line_alts_of demo_ws1 !!! 3%nat
               ++ pro_of (pro_from 1%nat [3%nat; 0%nat; 3%nat; 0%nat])).

Lemma demo_disc_seg'_panic : disc_seg' demo_seg_panic.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 0%nat; 3%nat; 0%nat] [3%nat]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* THE BANNER-LESS OPENING (the ruling of 2026-09-14): init's console open
   failed, it printed nothing, and the shell's "$ " is the round's first
   byte *)
Definition demo_seg_noban : list mobs :=
  demo_out u_prompt ++ [ObsUartIn Uart0 (Z_to_bv 8 101%Z)].

Lemma demo_disc_seg'_noban : disc_seg' demo_seg_noban.
Proof.
  eapply (disc_seg'_intro _ [0%nat] []);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* THE BURST: the whole command line typed before any of it is echoed.
   After init's banner and sh's prompt, all eight bytes of [echo hi] and
   its newline arrive as inputs with NOTHING on the wire between them; only
   then do the eight echoes go out, and then [hi], the newline and the next
   prompt.  This is the anti-vacuity check for the per-line rate bound: a
   whole line typed with none of it echoed yet is disciplined, and that is
   the one shape a per-BYTE bound would reject. *)
Definition demo_seg_burst : list mobs :=
  demo_out u_prologue
  ++ demo_in (wl_line demo_ws1)
  ++ demo_out (wl_line demo_ws1)
  ++ demo_out (line_alts_of demo_ws1 !!! 0%nat).

Lemma demo_disc_seg'_burst : disc_seg' demo_seg_burst.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 0%nat] [0%nat]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* THE DISCIPLINE, over the WHOLE history (uart-trace.md ruling 1): every
   cycle's input keeps the rate discipline.  [cycles_of h] lists every
   cycle, the open one LAST while the power is on, so the open cycle is
   covered. *)
Definition disc (h : list mobs) : Prop := Forall disc_seg' (cycles_of h).

Global Instance disc_dec h : Decision (disc h).
Proof. rewrite /disc. apply _. Qed.

Lemma disc_nil : disc [].
Proof. constructor. Qed.


(* ---- the three closure laws, at the SAME statements they had ---- *)

Lemma disc_seg'_other (seg : list mobs) (e : mobs) :
  not_cons_in e -> disc_seg' (seg ++ [e]) <-> disc_seg' seg.
Proof.
  intro He.
  assert (Hi : in_pres (seg ++ [e]) = in_pres seg)
    by (by apply in_pres_snoc_other).
  assert (Hn : ins (seg ++ [e]) = ins seg)
    by (rewrite ins_app (ins_snoc_other e He) app_nil_r; reflexivity).
  rewrite /disc_seg' /disc_seg Hi Hn. done.
Qed.

(* ...hence the closure law, at every I/O event the discipline cannot see:
   an output on either port, and an INPUT ON THE OTHER PORT.  The second is
   what a two-UART machine forces -- the environment may type on the
   kernel's port at any moment and the echo claim has to survive it. *)
Lemma disc_other (h : list mobs) (e : mobs) :
  is_io e = true -> not_cons_in e ->
  trace_shape h true ->
  disc (h ++ [e]) <-> disc h.
Proof.
  intros Hio He Hsh.
  destruct (cycles_of_io h [e] Hsh) as (cs & Hc & Hc');
    [by constructor|].
  rewrite /disc Hc Hc' !Forall_app !Forall_singleton
          (disc_seg'_other _ _ He). done.
Qed.

Lemma disc_seg'_out (seg : list mobs) (i : uart_id) (b : bv 8) :
  disc_seg' (seg ++ [ObsUartOut i b]) <-> disc_seg' seg.
Proof. apply disc_seg'_other. by destruct i. Qed.

Lemma disc_out (h : list mobs) (i : uart_id) (b : bv 8) :
  trace_shape h true ->
  disc (h ++ [ObsUartOut i b]) <-> disc h.
Proof. intro Hsh. apply disc_other; [by destruct i|by destruct i|exact Hsh]. Qed.

Lemma disc_power (h : list mobs) (on : bool) :
  disc (h ++ [if on then ObsPowerOff else ObsPowerOn]) <-> disc h.
Proof.
  rewrite /disc. destruct on.
  - by rewrite cycles_of_off.
  - rewrite cycles_of_on Forall_app Forall_singleton.
    split; [by intros [? _] | intros ?; split; [done | exact disc_seg'_nil]].
Qed.


Lemma disc_seg'_in (seg : list mobs) (b : bv 8) :
  disc_seg' (seg ++ [ObsUartIn Uart0 b]) -> disc_seg' seg.
Proof.
  intros [Hd (ps & cs & Hl & Hf & Hall)].
  rewrite /disc_seg ins_app ins_in in Hd.
  rewrite ins_app ins_in in Hl.
  assert (Hle : (nlines (ins seg) <= nlines (ins seg ++ [b]))%nat)
    by (apply nlines_prefix; by eexists).
  split; [exact (disc_input_snoc _ _ Hd) |].
  exists ps, (take (nlines (ins seg)) cs).
  split; [rewrite length_take Hl Nat.min_l; [done | exact Hle] |].
  split; [by apply Forall_take |].
  intros p Hp.
  assert (Hpin : p ∈ in_pres (seg ++ [ObsUartIn Uart0 b])).
  { rewrite in_pres_in. apply elem_of_app. by left. }
  destruct (Hall p Hpin) as [[HF Hlt] Hpt].
  assert (Hplt : (nlines (ins p) <= nlines (ins seg))%nat).
  { apply nlines_prefix.
    apply ins_prefix.
    exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp). }
  split.
  - rewrite /pro_ok. split; [exact HF |].
    by rewrite (pro_idx_take cs _ (nlines (ins p)) Hplt).
  - rewrite /disc_pt.
    assert (Hdn : (nlines (done_of (ins p)) <= nlines (ins seg))%nat)
      by (rewrite nlines_done; exact Hplt).
    rewrite (sess_take ps cs (done_of (ins p)) _ Hdn). exact Hpt.
Qed.

Lemma disc_in (h : list mobs) (b : bv 8) :
  trace_shape h true ->
  disc (h ++ [ObsUartIn Uart0 b]) -> disc h.
Proof.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartIn Uart0 b] Hsh) as (cs & Hc & Hc');
    [by constructor|].
  rewrite /disc Hc Hc' !Forall_app !Forall_singleton.
  intros [Hall Hseg]. split; [exact Hall|]. exact (disc_seg'_in _ _ Hseg).
Qed.

(* THE DISCIPLINE IS PREFIX-CLOSED, at ONE fact and with no [trace_shape]
   premise: [cyc_step] extends the most recent cycle (or starts one) and
   never touches an older one, so dropping the last event either drops a
   whole cycle or shortens the open one -- and [disc_seg'] is closed under
   both.  Every consumer that has to say "the history this log entry was
   taken at is disciplined too" spends this and nothing else. *)
Lemma Forall_rev_iff {A} (P : A -> Prop) (l : list A) :
  Forall P (rev l) <-> Forall P l.
Proof.
  induction l as [|a l IH]; [done|]. cbn.
  rewrite Forall_app Forall_singleton Forall_cons IH. tauto.
Qed.

Lemma disc_snoc (h : list mobs) (e : mobs) : disc (h ++ [e]) -> disc h.
Proof.
  rewrite /disc /cycles_of !Forall_rev_iff cycles_rev_app /=.
  destruct e as [i b|i b| |]; cbn.
  - destruct (cycles_rev h) as [|c cs]; [by intros _|].
    rewrite !Forall_cons. intros [Hseg Hall]. split; [|exact Hall].
    destruct i.
    + exact (disc_seg'_in c b Hseg).
    + apply (disc_seg'_other c (ObsUartIn Uart1 b) I). exact Hseg.
  - destruct (cycles_rev h) as [|c cs]; [by intros _|].
    rewrite !Forall_cons. intros [Hseg Hall]. split; [|exact Hall].
    apply (disc_seg'_out c i b). exact Hseg.
  - rewrite Forall_cons. by intros [_ ?].
  - done.
Qed.

Lemma disc_prefix (h' h : list mobs) : h' `prefix_of` h -> disc h -> disc h'.
Proof.
  intros [k ->]. induction k as [|e k IH] using rev_ind; intros Hd.
  - by rewrite app_nil_r in Hd.
  - apply IH. rewrite app_assoc in Hd. exact (disc_snoc _ _ Hd).
Qed.

(* ====================================================================== *)
(*  5.  THE CLAIM (R5)                                                    *)
(* ====================================================================== *)

(* THE OUTPUT CLAIM for one power cycle: everything that reached the
   console wire is a PREFIX of the transcript this cycle's input calls
   for, under some resolution of the per-line alternatives.  Nothing else
   is on this wire -- the kernel's own messages go to the other port -- so
   there is no interleaving to name and no witness to exhibit: the claim
   is a prefix test on the raw wire. *)
Definition good_out (seg : list mobs) : Prop :=
  expected_rel (ins seg) (obs_wire Uart0 seg).

Lemma good_out_nil : good_out [].
Proof.
  exists [0%nat], []. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* ...and it is not vacuous either: the six schedules the section above
   exhibits -- the two-line session, one exec failure, the fork failure,
   the shell that died on its own fork panic and was restarted, the
   banner-less opening, and the line typed as a burst -- satisfy it. *)
Lemma demo_good_out2 : good_out demo_seg2.
Proof.
  exists [3%nat; 0%nat], [0%nat; 0%nat].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_exec : good_out demo_seg_exec.
Proof.
  exists [3%nat; 1%nat; 3%nat; 0%nat], [].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_fork : good_out demo_seg_fork.
Proof.
  exists [3%nat; 2%nat], []. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_panic : good_out demo_seg_panic.
Proof.
  exists [3%nat; 0%nat; 3%nat; 0%nat], [3%nat].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_noban : good_out demo_seg_noban.
Proof.
  exists [0%nat], []. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_burst : good_out demo_seg_burst.
Proof.
  exists [3%nat; 0%nat], [0%nat].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.
