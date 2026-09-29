(* EchoOutPure.v -- THE PURE HALF OF E5's APPLICATION CLAIM.

   Design of record: claude-notes/projects/app-echo.md, "E5 -- THE CONSOLE
   I/O CLAIM: DESIGN OF RECORD" (the claim's pure conjuncts and the three
   arguments (E), (R), (W)); claude-notes/projects/echo-any-line.md, "The
   design (owner's session, 2026-09-16)" for the line-per-round session.
   This file is Iris-free list algebra over [EchoDisc] and [ConsLog], so
   that the Iris lane (ECHO-OUT) only has to APPLY lemmas.

   THE STAGE MACHINE.  The claim's data is the list [E] of ECHOED inputs:
   [E]'s j-th entry is the pair (history, byte) of input j+1, and the
   kernel put [echo_of c] on the wire for it.  The console's accepted
   bytes are then

     acc = D ps cs E ++ w      with   w `prefix_of` pending ps cs E

   where [D ps cs E] is the transcript DUE after E's last echo and
   [pending ps cs E] is the PROCESS output owed at that stage (init's
   banner and sh's first prompt before any input; the completed line's
   continuation at a line boundary; nothing mid-line -- mid-line a process
   byte is forbidden outright, which is what makes the discipline's rate
   bound bite).  [ps] and [cs] resolve the prologue's and the per-line
   alternatives, exactly as in [EchoDisc.sess].

   THE STAGE IS THE INPUT, NOT ITS LENGTH.  Everything below recurses over
   the bytes of [E] with the input read so far as the accumulator, and
   every "which round is this" test is [EchoDisc]'s parse -- [nlines],
   [rest_of], [nstarted] -- so each round carries its own line.

   THE FOUR FACTS, in the order the Iris claim spends them:
     F1  the stage is below the session   ([D_pending_sess], [D_stage_prefix])
     F2  the owed output is complete     ([next_input_of_complete])
     F3  the read window is a slice of E  ([read_window_prefix])
     F4  PHI's pure part                  ([good_out_of_stage]) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.       (* the parse: [bodies_of], [rest_of], [nlines] *)
Require Import EchoDisc.
Require Import ConsLog.
(* as in EchoDisc: a pure file does not inherit ssreflect's [rewrite] from
   the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  TWO BORROWED LEMMAS                                                *)
(*                                                                        *)
(*  The periodicity lemmas this file reads ([star_prefix_lookup] and its   *)
(*  two steps) are [EchoDisc]'s since lane ECHO-PURE moved them there.     *)
(*  What is still borrowed is the cycle a history's last input lives in:   *)
(*  it is an [ObsTrace]-level fact and belongs there, but the only copy    *)
(*  today is [UkSh]'s, far above this file.                               *)
(* ====================================================================== *)

(* ...and the cycle a history's last input lives in, copied from
   [UkSh.ush_cycles_snoc_in] for the same reason (that file is above this
   one; the fact is [ObsTrace]'s and belongs there). *)
Lemma epu_elem_of_rev_head {A} (x : A) (l : list A) : x ∈ rev (x :: l).
Proof. cbn. apply elem_of_app. right. by apply list_elem_of_singleton. Qed.

Lemma epu_cycles_snoc_in (h : list mobs) (b : bv 8) :
  exists s0 : list mobs,
    (s0 ++ [ObsUartIn Uart0 b])%list ∈ cycles_of (h ++ [ObsUartIn Uart0 b])%list.
Proof.
  rewrite /cycles_of cycles_rev_app.
  destruct (cycles_rev h) as [| c cs] eqn:Hc.
  - exists []. exact (epu_elem_of_rev_head ([] ++ [ObsUartIn Uart0 b])%list []).
  - exists c. exact (epu_elem_of_rev_head (c ++ [ObsUartIn Uart0 b])%list cs).
Qed.

(* ====================================================================== *)
(*  1.  THE BYTES OF THE LINE                                              *)
(* ====================================================================== *)

(* [echo_of] is the identity off '\r' *)
Lemma echo_of_other (c : bv 8) :
  c <> (mword_of_int 13 : mword 8) -> echo_of c = c.
Proof.
  intro Hne. rewrite /echo_of.
  destruct (eq_vec (c : mword 8) (mword_of_int 13 : mword 8)) eqn:He;
    [ | reflexivity ].
  exfalso. apply Hne. by apply eq_vec_true_iff in He.
Qed.

(* a byte is not a given one when its NUMBER is not -- the step that lets
   every refutation below be [lia] against [EchoDisc.disc_input_byte_val] *)
Local Lemma echo_byte_ne (c : bv 8) (z : Z) :
  bv_unsigned c <> z ->
  bv_unsigned (mword_of_int z : mword 8) = z ->
  eq_vec (c : mword 8) (mword_of_int z : mword 8) = false.
Proof.
  intros Hne Hz. apply eq_vec_false_iff. intro Hq.
  apply (f_equal bv_unsigned) in Hq. rewrite Hz in Hq. exact (Hne Hq).
Qed.

(* A DISCIPLINED INPUT HOLDS NO '\r', NO ERASE BYTE AND NO ^D, at any line.
   The third clause is what refutes the READ PATH'S SWALLOW arm (a leading
   ^D pops a byte and delivers nothing); the erase clause refutes the gap
   clause's erase disjunct.  Both used to be decided at a literal line of
   seventeen bytes; they are now one [lia] against the discipline's own
   byte reading. *)
Lemma disc_byte_ok (I : list (bv 8)) (c : bv 8) :
  disc_input I -> c ∈ I ->
  c <> (mword_of_int 13 : mword 8) /\ cons_erase c = false
  /\ bv_unsigned c <> 4%Z.
Proof.
  intros Hd Hc. pose proof (disc_input_byte_val I c Hd Hc) as Hv.
  split_and!.
  - intro Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
      [lia | by vm_compute].
  - rewrite /cons_erase.
    rewrite (echo_byte_ne c 21 ltac:(lia) ltac:(by vm_compute)).
    rewrite (echo_byte_ne c 8 ltac:(lia) ltac:(by vm_compute)).
    rewrite (echo_byte_ne c 127 ltac:(lia) ltac:(by vm_compute)).
    reflexivity.
  - lia.
Qed.

(* THE ECHO OF A DISCIPLINED BYTE IS THE BYTE ITSELF -- which is why [D]'s
   [echo_of c] and [sess]'s echo half are the same bytes. *)
Lemma echo_of_disc (I : list (bv 8)) (c : bv 8) :
  disc_input I -> c ∈ I -> echo_of c = c.
Proof. intros Hd Hc. apply echo_of_other, (disc_byte_ok I c Hd Hc). Qed.

(* THE BYTE A HISTORY ENDS IN IS ONE OF ITS INPUTS.  With the line fixed
   this said WHICH byte, by position; at a line per round the position says
   nothing and membership says everything the refutations need. *)
Lemma disc_seg_last_in (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> c ∈ ins h.
Proof.
  intros _ [h0 ->]. rewrite ins_app ins_in.
  apply elem_of_app. right. apply list_elem_of_here.
Qed.

(* the refutation the read contract's erase disjunct needs *)
Lemma disc_seg_no_erase (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> cons_erase c = false.
Proof.
  intros Hd He.
  apply (disc_byte_ok (ins h) c Hd (disc_seg_last_in h c Hd He)).
Qed.

(* ...and the same for the read path's SWALLOW arm.  The kernel tests
   [cons_xlate b] against 0x04 and [cons_xlate] is the identity off '\r'
   ([UkSh.disc_no_ctrl_d] is that bridge); this is its pure half, which is
   all a file below ConsoleInv can say. *)
Lemma disc_seg_no_ctrl_d (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> bv_unsigned c <> 4%Z.
Proof.
  intros Hd He.
  apply (disc_byte_ok (ins h) c Hd (disc_seg_last_in h c Hd He)).
Qed.

Lemma disc_no_erase (h : list mobs) (c : bv 8) :
  disc h -> obs_ends_in Uart0 h c -> cons_erase c = false.
Proof.
  intros Hdisc [h0 ->].
  destruct (epu_cycles_snoc_in h0 c) as (s0 & Hin).
  apply list_elem_of_lookup in Hin as [i Hi].
  pose proof (disc_seg'_proj _ (Forall_lookup_1 _ _ _ _ Hdisc Hi)) as Hseg.
  eapply disc_seg_no_erase; [exact Hseg | apply obs_ends_in_snoc].
Qed.

(* THE OPEN CYCLE OF A DISCIPLINED HISTORY KEEPS D3 -- the one step from
   the whole-history discipline to the segment the claim is stated over. *)
Lemma disc_seg_open_seg (h : list mobs) :
  trace_shape h true -> disc h -> disc_seg (open_seg h).
Proof.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply list_elem_of_lookup in Hin as [i Hi].
  exact (disc_seg'_proj _ (Forall_lookup_1 _ _ _ _ Hd Hi)).
Qed.

(* ...AND THE BYTE COMES WITH IT.  Lane ECHO-OUT stores E's histories as
   CYCLE SEGMENTS (the discipline, [good_out] and [acc] are all per power
   cycle, so [E_index]'s [ins] must count the cycle's inputs and not the
   run's), and this is what turns the shift's [obs_ends_in] at the whole
   history into the one at the segment. *)
Lemma open_seg_ends_in (h : list mobs) (c : bv 8) :
  obs_ends_in Uart0 h c -> obs_ends_in Uart0 (open_seg h) c.
Proof.
  intros [h0 ->].
  rewrite (open_seg_io h0 [ObsUartIn Uart0 c]); [| by repeat constructor].
  apply obs_ends_in_snoc.
Qed.

(* ====================================================================== *)
(*  2.  THE STAGE MACHINE: [pending] AND [D]                               *)
(* ====================================================================== *)

(* THE PROCESS OUTPUT OWED AT INPUT [I].  Before any input it is init's
   banner and sh's first prompt ([pro_of ps]); after the '\n' echo that
   completed the last body it is that line's continuation, indexed exactly
   as [EchoDisc.alt_blk] indexes it; mid-line it is nothing.  It reads the
   INPUT, through the parse, because [EchoDisc.sess] does. *)
Definition pending_at (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then pro_of ps
  else if decide (rest_of I = [])
       then alt_cont ps cs (bodies_of I) (nlines I - 1) else [].

Definition pending (ps cs : list nat) (E : list (list mobs * bv 8))
  : list (bv 8) := pending_at ps cs (snd <$> E).

(* ---- THE BYTES OF AN INPUT'S FIRST [n] COMPLETE LINES ---------------- *)

(* [lines_bytes I n] counts the first [n] complete lines of [I], each with
   the newline that closed it.  It is the yardstick the claim's
   DELIVERED-COUNT clause is stated in -- "every completed line whose block
   has begun has been consumed" is [lines_bytes Eb q <= length dl] -- and
   that clause is what bounds the console ring: with at most the line in
   progress unconsumed, and [EchoDisc.line_max] keeping a line under the
   ring's 128, a full ring is impossible ([drop_refuted]). *)
Definition lines_bytes (I : list (bv 8)) (n : nat) : nat :=
  length (wl_join (take n (bodies_of I))).

Lemma lines_bytes_0 (I : list (bv 8)) : lines_bytes I 0%nat = 0%nat.
Proof. by rewrite /lines_bytes take_0 wl_join_nil. Qed.

(* the two snoc steps: a byte inside a line adds nothing to any count, and
   the newline that closes line [nlines I] leaves the counts below it *)
Lemma lines_bytes_snoc_other (I : list (bv 8)) (b : bv 8) (n : nat) :
  b <> wl_nl -> lines_bytes (I ++ [b]) n = lines_bytes I n.
Proof. intro Hb. by rewrite /lines_bytes (bodies_of_snoc_other I b Hb). Qed.

Lemma lines_bytes_snoc_nl (I : list (bv 8)) (n : nat) :
  (n <= nlines I)%nat -> lines_bytes (I ++ [wl_nl]) n = lines_bytes I n.
Proof.
  intro Hn. rewrite /lines_bytes bodies_of_snoc_nl.
  rewrite (take_app_le (bodies_of I) [rest_of I] n); [reflexivity |].
  rewrite /nlines in Hn. exact Hn.
Qed.

(* ...one more line is more bytes *)
Lemma lines_bytes_S (I : list (bv 8)) (n : nat) (l : list (bv 8)) :
  bodies_of I !! n = Some l ->
  lines_bytes I (S n) = (lines_bytes I n + length l + 1)%nat.
Proof.
  intro Hl. rewrite /lines_bytes (take_S_r _ _ _ Hl) wl_join_snoc !length_app.
  cbn [length]. lia.
Qed.

Lemma lines_bytes_le (I : list (bv 8)) (n m : nat) :
  (n <= m)%nat -> (lines_bytes I n <= lines_bytes I m)%nat.
Proof.
  intro Hnm. rewrite /lines_bytes. apply prefix_length.
  destruct (prefix_take_le (bodies_of I) n m Hnm) as [bs Hbs].
  exists (wl_join bs). by rewrite Hbs wl_join_app.
Qed.

(* ALL the complete lines are the input minus the line in progress *)
Lemma lines_bytes_nlines (I : list (bv 8)) :
  lines_bytes I (nlines I) = length (done_of I).
Proof. rewrite /lines_bytes /nlines take_ge; [reflexivity | lia]. Qed.

Lemma lines_bytes_all (I : list (bv 8)) :
  lines_bytes I (nlines I) = (length I - length (rest_of I))%nat.
Proof. rewrite lines_bytes_nlines. exact (length_done_of I). Qed.

Lemma lines_bytes_rest (I : list (bv 8)) :
  (lines_bytes I (nlines I) + length (rest_of I))%nat = length I.
Proof.
  rewrite lines_bytes_nlines -{3}(done_of_app_rest I) length_app. lia.
Qed.

(* ...and the LAST of them costs its own body plus its newline *)
Lemma lines_bytes_last (I : list (bv 8)) :
  (0 < nlines I)%nat ->
  lines_bytes I (nlines I)
  = (lines_bytes I (nlines I - 1)%nat
     + length (bodies_of I !!! (nlines I - 1)%nat) + 1)%nat.
Proof.
  intro Hq.
  assert (Hk : (nlines I - 1 < length (bodies_of I))%nat)
    by (rewrite /nlines in Hq |- *; lia).
  destruct (lookup_lt_is_Some_2 (bodies_of I) (nlines I - 1)%nat Hk) as [l Hl].
  rewrite (list_lookup_total_correct _ _ _ Hl).
  replace (nlines I) with (S (nlines I - 1)%nat) at 1 by lia.
  exact (lines_bytes_S I (nlines I - 1)%nat l Hl).
Qed.

(* THE RING BOUND, as pure arithmetic: under D3 an input is its complete
   lines plus at most one line's worth of bytes -- whether the last line
   counted is the one before the input's end or the input's own last. *)
Lemma lines_bytes_disc_bound (I : list (bv 8)) (n : nat) :
  disc_input I ->
  (n = nlines I \/ (rest_of I = [] /\ n = (nlines I - 1)%nat)) ->
  (length I <= lines_bytes I n + line_max)%nat.
Proof.
  intros Hd Hn.
  pose proof (lines_bytes_rest I) as Hsum.
  destruct Hn as [-> | [Hr ->]].
  - pose proof (disc_input_rest_short I Hd). lia.
  - destruct (decide (0 < nlines I)%nat) as [Hpos | Hz].
    + rewrite (lines_bytes_last I Hpos) in Hsum.
      assert (Hk : (nlines I - 1 < length (bodies_of I))%nat)
        by (rewrite /nlines in Hpos |- *; lia).
      destruct (lookup_lt_is_Some_2 (bodies_of I) (nlines I - 1)%nat Hk)
        as [l Hl].
      rewrite (list_lookup_total_correct _ _ _ Hl) in Hsum.
      pose proof (body_ok_short l (disc_input_body I _ l Hd Hl)).
      rewrite Hr in Hsum. cbn [length] in Hsum. lia.
    + assert (Hnl : nlines I = 0%nat) by lia.
      rewrite Hnl lines_bytes_0 Hr in Hsum. cbn [length] in Hsum. lia.
Qed.

(* THE TRANSCRIPT DUE AFTER E's LAST ECHO.  The note's law is a RIGHT
   append ([D cs (E ++ [(h,c)]) = D cs E ++ pending cs E ++ [echo_of c]]),
   but a [Fixpoint] on the right does not reduce under [cbn] on an opaque
   tail.  So the definition is structural on [E] FROM THE LEFT with the
   INPUT READ SO FAR as the accumulator: [cbn] reduces it on every
   [x :: E'], and the note's law is [D_app] below, one line off
   [D_from_app]. *)
Fixpoint D_from (ps cs : list nat) (pre : list (bv 8))
    (E : list (list mobs * bv 8)) : list (bv 8) :=
  match E with
  | [] => []
  | x :: E' => pending_at ps cs pre ++ [echo_of x.2]
               ++ D_from ps cs (pre ++ [x.2]) E'
  end.

Definition D (ps cs : list nat) (E : list (list mobs * bv 8)) : list (bv 8) :=
  D_from ps cs [] E.

Lemma D_nil ps cs : D ps cs [] = [].
Proof. reflexivity. Qed.

Lemma pending_at_nil ps cs : pending_at ps cs [] = pro_of ps.
Proof.
  rewrite /pending_at. case_decide as H; [done | by destruct (H eq_refl)].
Qed.

Lemma pending_nil ps cs : pending ps cs [] = pro_of ps.
Proof. rewrite /pending fmap_nil. exact (pending_at_nil ps cs). Qed.

(* the two extension laws the stage spends: a block STRICTLY BELOW the
   current stage reads a round that has settled, so a lower bound of [ps]
   already determines it. *)
Lemma pending_at_ps_ext ps ps' cs I :
  ps `prefix_of` ps' ->
  (pro_idx cs (nlines I) < pro_rounds ps)%nat ->
  pending_at ps cs I = pending_at ps' cs I.
Proof.
  intros Hp Hr. rewrite /pending_at. case_decide as H0.
  { subst I. apply (pro_of_from_done_ext 0%nat); [exact Hp |].
    rewrite nlines_nil in Hr. cbn [pro_idx] in Hr. exact Hr. }
  case_decide as Hm; [| done].
  rewrite /alt_cont. f_equal. case_decide as H3; [| done].
  pose proof (nlines_pos_of_rest_nil I H0 Hm) as Hq.
  assert (Hs : S (pro_idx cs (nlines I - 1)) = pro_idx cs (nlines I)).
  { replace (nlines I) with (S (nlines I - 1)) at 2 by lia.
    symmetry. apply pro_idx_S3.
    replace (S (nlines I - 1) - 1)%nat with (nlines I - 1)%nat by lia.
    exact H3. }
  rewrite Hs. by apply pro_of_from_done_ext.
Qed.

Lemma pending_at_ps_mono ps ps' cs I :
  ps `prefix_of` ps' -> pending_at ps cs I `prefix_of` pending_at ps' cs I.
Proof.
  intros Hp. rewrite /pending_at. case_decide as H0.
  { by apply pro_of_mono. }
  case_decide as Hm; [| reflexivity].
  rewrite /alt_cont. apply prefix_app. case_decide as H3; [| reflexivity].
  by apply pro_of_from_mono.
Qed.

Lemma pending_ps_mono ps ps' cs E :
  ps `prefix_of` ps' -> pending ps cs E `prefix_of` pending ps' cs E.
Proof. intro Hp. by apply pending_at_ps_mono. Qed.

(* THE ROUND-OPENING BLOCK'S SHAPE.  A block that OPENS a prologue round --
   the head of the transcript (no input yet), or a line whose continuation
   was the shell's own fork panic -- owes the panic line, if any, and then
   THAT ROUND'S PROLOGUE.  The panic line is a CONSTANT ([alt_panic]), not
   a function of what was typed, which is why this equation survives a line
   per round.  Every OTHER block owes no prologue at all, so the
   round-opening disjunction is a premise and not decoration. *)
Lemma pending_at_round_pre (ps cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ cs !!! (nlines I - 1)%nat = 3%nat) ->
  pending_at ps cs I
  = (if decide (I = []) then [] else alt_panic)
    ++ pro_of (pro_from (pro_idx cs (nlines I)) ps).
Proof.
  intros Hm Hopen. rewrite /pending_at. case_decide as H0.
  - subst I. rewrite nlines_nil. by cbn [pro_idx pro_from app].
  - rewrite decide_True; [| exact Hm].
    assert (H3 : cs !!! (nlines I - 1)%nat = 3%nat).
    { destruct Hopen as [Hn | H3]; [by destruct (H0 Hn) | exact H3]. }
    pose proof (nlines_pos_of_rest_nil I H0 Hm) as Hq.
    assert (Hs : S (pro_idx cs (nlines I - 1)) = pro_idx cs (nlines I)).
    { replace (nlines I) with (S (nlines I - 1)) at 2 by lia.
      symmetry. apply pro_idx_S3.
      replace (S (nlines I - 1) - 1)%nat with (nlines I - 1)%nat by lia.
      exact H3. }
    rewrite /alt_cont. case_decide as H4; [| by destruct (H4 H3)].
    rewrite Hs H3 line_alts_of_3. reflexivity.
Qed.

(* A ROUND-OPENING BLOCK STANDS AT A ROUND THE STAGE HAS ALREADY REACHED:
   the block below it is settled ([pro_pin]) and this one is the next, so
   the round's index never runs past what the resolution has resolved.  This
   is the LOWER bound on [pro_rounds] the prologue-choice write pairs with
   the upper bound its own [~ pro_done] gives. *)
Lemma pro_pin_round_le (ps cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ cs !!! (nlines I - 1)%nat = 3%nat) ->
  pro_pin ps cs I ->
  (pro_idx cs (nlines I) <= pro_rounds ps)%nat.
Proof.
  intros Hm Ho Hpin. destruct (decide (I = [])) as [-> | Hn0].
  { rewrite nlines_nil. cbn [pro_idx]. lia. }
  assert (H3 : cs !!! (nlines I - 1)%nat = 3%nat)
    by (destruct Ho as [Hz | H3]; [by destruct (Hn0 Hz) | exact H3]).
  pose proof (nlines_pos_of_rest_nil I Hn0 Hm) as Hq.
  assert (Hs : S (pro_idx cs (nlines I - 1)) = pro_idx cs (nlines I)).
  { replace (nlines I) with (S (nlines I - 1)) at 2 by lia.
    symmetry. apply pro_idx_S3.
    replace (S (nlines I - 1) - 1)%nat with (nlines I - 1)%nat by lia.
    exact H3. }
  assert (Hlt : (nlines I - 1 < nstarted I)%nat)
    by (pose proof (nlines_le_nstarted I); lia).
  pose proof (Hpin (nlines I - 1)%nat Hlt). lia.
Qed.

(* ...so two resolutions that owe the SAME round-opening block agree on that
   round's prologue.  This is the fact the prologue-choice write reconciles
   its own [ps0] against the claim's authority with. *)
Lemma pending_at_round_det (ps ps' cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ cs !!! (nlines I - 1)%nat = 3%nat) ->
  pending_at ps cs I = pending_at ps' cs I ->
  pro_of (pro_from (pro_idx cs (nlines I)) ps)
  = pro_of (pro_from (pro_idx cs (nlines I)) ps').
Proof.
  intros Hm Hopen Heq.
  rewrite (pending_at_round_pre ps cs I Hm Hopen) in Heq.
  rewrite (pending_at_round_pre ps' cs I Hm Hopen) in Heq.
  by apply app_inv_head in Heq.
Qed.

(* ---- the append laws ---- *)

Lemma epu_app_snoc {A} (pre : list A) (a : A) (l : list A) :
  (pre ++ [a]) ++ l = pre ++ a :: l.
Proof. by rewrite -app_assoc. Qed.

Lemma epu_app_cons_ne {A} (l : list A) (a : A) (r : list A) :
  l <> l ++ a :: r.
Proof.
  intro Hq. apply (f_equal length) in Hq.
  rewrite (length_app l (a :: r)) in Hq. cbn [length] in Hq. lia.
Qed.

Lemma D_from_pending_ext ps ps' cs pre E :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ (snd <$> E) ->
     J <> pre ++ (snd <$> E) -> pending_at ps cs J = pending_at ps' cs J) ->
  D_from ps cs pre E = D_from ps' cs pre E.
Proof.
  revert pre. induction E as [| x E IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [x.2]) ++ (snd <$> E) = pre ++ (snd <$> (x :: E)))
    by (by rewrite fmap_cons epu_app_snoc).
  assert (Hhere : pending_at ps cs pre = pending_at ps' cs pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - rewrite fmap_cons. apply (epu_app_cons_ne pre x.2 (snd <$> E)). }
  cbn [D_from]. rewrite Hhere. do 2 f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma D_ps_ext ps ps' cs E :
  ps `prefix_of` ps' -> pro_pin ps cs (snd <$> E) -> D ps cs E = D ps' cs E.
Proof.
  intros Hp Hpin. rewrite /D. apply D_from_pending_ext.
  intros J H1 H2 H3. rewrite app_nil_l in H2, H3.
  apply (pending_at_ps_ext ps ps' cs J Hp).
  apply Hpin. exact (nstarted_strict J (snd <$> E) H2 H3).
Qed.

Lemma D_from_app ps cs pre E1 E2 :
  D_from ps cs pre (E1 ++ E2)
  = D_from ps cs pre E1 ++ D_from ps cs (pre ++ (snd <$> E1)) E2.
Proof.
  revert pre. induction E1 as [| x E1 IH]; intros pre.
  - cbn [D_from app]. by rewrite fmap_nil app_nil_r.
  - change ((x :: E1) ++ E2) with (x :: (E1 ++ E2)).
    cbn [D_from]. rewrite (IH (pre ++ [x.2])) fmap_cons epu_app_snoc.
    by rewrite -!app_assoc.
Qed.

(* THE NOTE'S LAW, verbatim *)
Lemma D_app ps cs E x :
  D ps cs (E ++ [x]) = D ps cs E ++ pending ps cs E ++ [echo_of x.2].
Proof.
  rewrite /D /pending D_from_app app_nil_l /=. by rewrite ?app_nil_r.
Qed.

(* ====================================================================== *)
(*  3.  WHAT THE CLAIM SAYS ABOUT [E]                                      *)
(* ====================================================================== *)

(* E's INDEX LAW, as the design states it: E's j-th entry is input j+1, and
   its byte is the one its history ends in. *)
Definition E_index (E : list (list mobs * bv 8)) : Prop :=
  forall (j : nat) (x : list mobs * bv 8),
    E !! j = Some x -> obs_ends_in Uart0 x.1 x.2 /\ length (ins x.1) = S j.

(* E's CONTENT LAW: the bytes of E ARE a disciplined input.  THIS IS THE
   HYPOTHESIS F1 TURNS ON and the note does not list it: [D] records the
   bytes actually echoed and [sess] records the input's own, so without it
   [D ps cs E] and [sess ps cs (snd <$> E)] are unrelated.  It is not a new
   assumption -- it is D3 at the cycle segment ([E_disc_of_hist]) -- but it
   has to be NAMED, because F1 is stated at stages where the discipline
   itself is not in scope.

   IT REPLACES A POSITIONAL LAW.  With one fixed line the same fact read
   "E's j-th byte is byte [j mod 17] of the line"; at a line per round no
   position determines a byte, and what is left is exactly that the bytes
   parse. *)
Definition E_disc (E : list (list mobs * bv 8)) : Prop :=
  disc_input (snd <$> E).

Lemma epu_fmap_prefix {A B} (f : A -> B) (l l' : list A) :
  l `prefix_of` l' -> (f <$> l) `prefix_of` (f <$> l').
Proof. intros [k ->]. rewrite fmap_app. by eexists. Qed.

Lemma epu_Forall_drop {A} (P : A -> Prop) (n : nat) (l : list A) :
  Forall P l -> Forall P (drop n l).
Proof.
  rewrite !Forall_lookup. intros HF i x Hx.
  rewrite lookup_drop in Hx. by eapply HF.
Qed.

Lemma E_disc_take (E : list (list mobs * bv 8)) (n : nat) :
  E_disc E -> E_disc (take n E).
Proof.
  rewrite /E_disc. intro HE.
  exact (disc_input_prefix _ _ (epu_fmap_prefix snd _ _ (prefix_take _ _)) HE).
Qed.

Lemma E_disc_app_l (E : list (list mobs * bv 8)) (x : list mobs * bv 8) :
  E_disc (E ++ [x]) -> E_disc E.
Proof. rewrite /E_disc fmap_app. apply disc_input_snoc. Qed.

Lemma E_disc_echo (E : list (list mobs * bv 8)) (j : nat)
    (x : list mobs * bv 8) :
  E_disc E -> E !! j = Some x -> echo_of x.2 = x.2.
Proof.
  intros HE Hx. apply (echo_of_disc (snd <$> E) x.2 HE).
  apply list_elem_of_lookup_2 with j. by rewrite list_lookup_fmap Hx.
Qed.

(* ...AND WHERE IT COMES FROM.  E's histories are snapshots of ONE cycle
   segment, and [E_index] puts entry [j]'s byte at position [j] of that
   segment's input, so the bytes of E ARE a prefix of it -- and the
   segment is disciplined. *)
Lemma E_length_le_hist (E : list (list mobs * bv 8)) (Sg : list mobs) :
  E_index E -> (forall j x, E !! j = Some x -> x.1 `prefix_of` Sg) ->
  (length E <= length (ins Sg))%nat.
Proof.
  intros Hidx Hpre.
  destruct (decide (length E = 0)%nat) as [H0 | H0]; [lia |].
  destruct (lookup_lt_is_Some_2 E (length E - 1)%nat ltac:(lia)) as [x Hx].
  destruct (Hidx _ x Hx) as [_ Hlx].
  pose proof (prefix_length _ _ (ins_prefix _ _ (Hpre _ x Hx))) as Hle. lia.
Qed.

Lemma E_bytes_of_hist (E : list (list mobs * bv 8)) (Sg : list mobs) :
  E_index E ->
  (forall j x, E !! j = Some x -> x.1 `prefix_of` Sg) ->
  (length E <= length (ins Sg))%nat ->
  (snd <$> E) = take (length E) (ins Sg).
Proof.
  intros Hidx Hpre Hlen. apply list_eq. intros j.
  destruct (decide (j < length E)%nat) as [Hj | Hj]; last first.
  { rewrite list_lookup_fmap (lookup_ge_None_2 E j ltac:(lia)) /=.
    symmetry. apply lookup_ge_None_2. rewrite length_take. lia. }
  destruct (lookup_lt_is_Some_2 E j Hj) as [x Hx].
  rewrite list_lookup_fmap Hx /= lookup_take_lt; [| exact Hj].
  destruct (Hidx j x Hx) as [[h0 Hh0] Hlx].
  rewrite Hh0 ins_app ins_in (length_app (ins h0) [x.2]) in Hlx.
  cbn [length] in Hlx.
  assert (Hlk : ins x.1 !! j = Some x.2).
  { rewrite Hh0 ins_app ins_in lookup_app_r; [| lia].
    replace (j - length (ins h0))%nat with 0%nat by lia. reflexivity. }
  symmetry.
  exact (prefix_lookup_Some _ _ _ _ Hlk (ins_prefix _ _ (Hpre j x Hx))).
Qed.

Lemma E_disc_of_hist (E : list (list mobs * bv 8)) (Sg : list mobs) :
  E_index E ->
  (forall j x, E !! j = Some x -> x.1 `prefix_of` Sg) ->
  disc_input (ins Sg) -> E_disc E.
Proof.
  intros Hidx Hpre Hd.
  pose proof (E_length_le_hist E Sg Hidx Hpre) as Hlen.
  rewrite /E_disc (E_bytes_of_hist E Sg Hidx Hpre Hlen).
  exact (disc_input_prefix _ _ (prefix_take _ _) Hd).
Qed.

Lemma E_index_take (E : list (list mobs * bv 8)) (n : nat) :
  E_index E -> E_index (take n E).
Proof.
  intros HE j x Hx. apply lookup_take_Some in Hx as [Hx _]. by apply HE.
Qed.

(* ====================================================================== *)
(*  4.  F1 -- THE STAGE IS BELOW THE SESSION                               *)
(* ====================================================================== *)

(* F1, THE BOUNDARY EQUATION.  Stated at EVERY stage, not only at a line
   boundary: mid-line [pending] is empty and the equation is the statement
   that the echoes so far ARE the line in progress.  The induction is over
   one echoed byte, and [EchoDisc]'s two snoc laws for [sess] are what make
   it a two-case split instead of a division. *)
Lemma D_pending_sess (ps cs : list nat) (E : list (list mobs * bv 8)) :
  E_disc E -> D ps cs E ++ pending ps cs E = sess ps cs (snd <$> E).
Proof.
  induction E as [| x E IH] using rev_ind; intros HE.
  - by rewrite D_nil pending_nil app_nil_l fmap_nil sess_nil.
  - pose proof (E_disc_app_l E x HE) as HE0.
    pose proof (IH HE0) as IH'. rewrite /pending in IH'.
    assert (Hb : echo_of x.2 = x.2).
    { apply (E_disc_echo (E ++ [x]) (length E) x HE).
      rewrite lookup_app_r; [by rewrite Nat.sub_diag | lia]. }
    assert (Hfm : (snd <$> (E ++ [x])) = (snd <$> E) ++ [x.2])
      by (by rewrite fmap_app).
    rewrite D_app /pending Hfm Hb.
    rewrite (app_assoc (D ps cs E) (pending_at ps cs (snd <$> E)) [x.2]) IH'.
    destruct (decide (x.2 = wl_nl)) as [Hnl | Hnl].
    + assert (Hp : pending_at ps cs ((snd <$> E) ++ [x.2])
                   = alt_cont ps cs
                       (bodies_of (snd <$> E) ++ [rest_of (snd <$> E)])
                       (nlines (snd <$> E))).
      { rewrite Hnl /pending_at. case_decide as H1.
        { exfalso. apply (f_equal length) in H1.
          rewrite (length_app (snd <$> E) [wl_nl]) in H1.
          cbn [length] in H1. lia. }
        rewrite decide_True; [| exact (rest_of_snoc_nl (snd <$> E))].
        rewrite bodies_of_snoc_nl nlines_snoc_nl.
        by replace (S (nlines (snd <$> E)) - 1)%nat
          with (nlines (snd <$> E)) by lia. }
      rewrite Hp Hnl sess_snoc_nl.
      by rewrite -(app_assoc (sess ps cs (snd <$> E)) [wl_nl] _).
    + assert (Hp : pending_at ps cs ((snd <$> E) ++ [x.2]) = []).
      { rewrite /pending_at. case_decide as H1.
        { exfalso. apply (f_equal length) in H1.
          rewrite (length_app (snd <$> E) [x.2]) in H1.
          cbn [length] in H1. lia. }
        rewrite decide_False; [done |].
        rewrite (rest_of_snoc_other (snd <$> E) x.2 Hnl).
        intro Hq. apply (f_equal length) in Hq.
        rewrite (length_app (rest_of (snd <$> E)) [x.2]) in Hq.
        cbn [length] in Hq. lia. }
      rewrite Hp app_nil_r (sess_snoc_other ps cs (snd <$> E) x.2 Hnl).
      reflexivity.
Qed.

(* F1, AS THE CLAIM USES IT *)
Lemma D_stage_prefix (ps cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) :
  E_disc E -> w `prefix_of` pending ps cs E ->
  (D ps cs E ++ w) `prefix_of` sess ps cs (snd <$> E).
Proof.
  intros HE Hw. rewrite -(D_pending_sess ps cs E HE).
  by apply prefix_app, Hw.
Qed.

(* the third side condition the note lists, [sess cs I ⊑ sess cs I'] for
   [I ⊑ I'], IS [EchoDisc.sess_mono] -- UNCONDITIONALLY, because the
   block's echo half is the raw body -- and is not restated here. *)

(* ====================================================================== *)
(*  5.  F2 -- THE NEXT ECHO IS THE NEXT INPUT                              *)
(* ====================================================================== *)

(* TWO PREFIX-COMPARABLE HISTORIES THAT END IN THE SAME INPUT NUMBER ARE
   EQUAL.  The note asks for this by name; it is what turns "the byte is
   already logged" into a contradiction with the log-order fact. *)
Lemma ins_hist_agree (h1 h2 : list mobs) (c1 c2 : bv 8) :
  h1 `prefix_of` h2 ->
  obs_ends_in Uart0 h1 c1 -> obs_ends_in Uart0 h2 c2 ->
  length (ins h1) = length (ins h2) -> h1 = h2.
Proof.
  intros [k ->] He1 He2 Hlen.
  rewrite ins_app length_app in Hlen.
  assert (Hk : ins k = []) by (apply nil_length_inv; lia).
  destruct k as [|e k _] using rev_ind; [by rewrite app_nil_r|].
  exfalso. destruct He2 as [h0 Hh0].
  rewrite app_assoc in Hh0.
  apply app_inj_tail in Hh0 as [_ ->].
  rewrite ins_app ins_in in Hk. by apply app_eq_nil in Hk as [_ ?].
Qed.


(* F2.  The wire is abstract ([W]) so that the Iris lane may instantiate it
   with [obs_wire Uart0 (open_seg h)] or with [obs_wire Uart0 h]; the two
   hypotheses about it are the discipline's LOWER bound at the input BEFORE
   this byte ([EchoDisc.disc_pt], D1) and the claim's UPPER bound.

   WHAT REPLACES THE LENGTH COMPARISON.  With a fixed line the two stages
   were two numbers and one was below the other by [sess]'s strict growth.
   Here they are two INPUTS -- and the point is that both are prefixes of
   the SAME history's input: [E_index] plus the log-order fact identify
   [snd <$> E] with [take (length E) (ins h)], and the discipline's bound
   is at [take (m - 1) (ins h)], so the two takes are comparable and
   [EchoDisc.sess_length_lt] decides which.

   HYPOTHESES THE NOTE DOES NOT LIST: [E_disc E] (F1 turns on it), and
   [Hnew] -- the new input's history strictly extends every logged one.
   [Hnew] is the kernel's own log-order fact (the design: "the kernel
   proves [h] is strictly above every history already in [pops]"), and
   without it nothing refutes [m <= length E]: an adversary log that
   records the SAME input twice satisfies every other hypothesis. *)
Lemma prefix_app_cancel {A} (k a b : list A) :
  (k ++ a) `prefix_of` (k ++ b) -> a `prefix_of` b.
Proof.
  intros [z Hz]. exists z. rewrite -app_assoc in Hz. by apply app_inv_head in Hz.
Qed.

Lemma hist_ext_irrefl (h : list mobs) : hist_ext h h -> False.
Proof. intros [_ Hl]. lia. Qed.


(* THE ECHO STEP'S FACT.  [w] -- the process output still owed at this
   stage -- IS the whole of it, so the echo about to go out is the next
   byte of the transcript and nothing of the process's is pending in front
   of it.

   WHERE THE TWO FACTS COME FROM.  That the echoed list holds every earlier
   input of the era ([length E = m - 1]) is the KERNEL's FIFO discipline --
   the receive FIFO is drained in arrival order and each popped byte's arm
   closes before the next pop -- handed to the claim as
   [ConsLog.cons_ev_ok]'s log-completeness clause together with the claim's
   own "every log entry is echoed".  It is not a trace fact, and it is a
   PREMISE here.  That the output is complete is the DISCIPLINE's, read at
   [LineWords.done_of]: at a line's first byte the bound is the full
   transcript for every completed line, and mid-line [pending] is empty, so
   there is nothing to be complete. *)
Lemma next_input_of_complete (ps cs : list nat) (E : list (list mobs * bv 8))
      (w W : list (bv 8)) (h : list mobs) (c : bv 8) (m : nat) :
  E_disc E -> E_index E ->
  (forall x, x ∈ E -> hist_ext x.1 h) ->
  obs_ends_in Uart0 h c ->
  length (ins h) = m ->
  length E = (m - 1)%nat ->
  w `prefix_of` pending ps cs E ->
  sess ps cs (done_of (take (m - 1)%nat (ins h))) `prefix_of` W ->
  W `prefix_of` (D ps cs E ++ w) ->
  w = pending ps cs E.
Proof.
  intros HEb HEi Hnew Hends Hm HlenE Hw Hlow Hup.
  assert (Hprefix : forall j x, E !! j = Some x -> x.1 `prefix_of` h).
  { intros j x Hx. apply (Hnew x). by eapply list_elem_of_lookup_2. }
  pose proof (E_length_le_hist E h HEi Hprefix) as Hle.
  pose proof (E_bytes_of_hist E h HEi Hprefix Hle) as HEq.
  rewrite HlenE in HEq.
  destruct (decide (rest_of (snd <$> E) = [])) as [Hr | Hr].
  - (* at a line boundary the truncation is the identity, and the stage
       plus what is owed IS the session *)
    apply (anti_symm prefix); [exact Hw |].
    eapply (prefix_app_cancel (D ps cs E)).
    rewrite (D_pending_sess ps cs E HEb).
    etrans; [| etrans; [exact Hlow | exact Hup] ].
    rewrite -HEq (done_of_rest_nil (snd <$> E) Hr). reflexivity.
  - (* mid-line nothing is owed, so [w] is empty and so is [pending] *)
    assert (Hne : (snd <$> E) <> []).
    { intro Hq. rewrite Hq rest_of_nil in Hr. by apply Hr. }
    assert (Hp : pending ps cs E = []).
    { rewrite /pending /pending_at decide_False; [| exact Hne].
      by rewrite decide_False. }
    rewrite Hp in Hw. rewrite Hp. by apply prefix_nil_inv.
Qed.

(* ---- THE DROP ARM IS REFUTED ----------------------------------------- *)

(* [ConsLog.cons_drop_ok] says why a [consoleintr] arm echoed nothing: a
   NUL, a ^P, an erase with nothing to erase, or a FULL RING.  The first
   three are refuted by D3 -- a disciplined input holds none of those bytes
   -- and the fourth by the ring bound: the era's log holds every earlier
   input ([ConsLog.cons_ev_ok]'s log-completeness clause), the claim has
   echoed every one of them, and the claim's delivered-count clause says
   every completed line whose block has begun is consumed.  So what the
   ring can still hold is the line in progress, which [EchoDisc.line_max]
   keeps under 128. *)

Lemma epu_filter_all {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (l : list A) : Forall P l -> filter P l = l.
Proof.
  induction l as [| x l IH]; intro HF; [by rewrite filter_nil |].
  destruct (Forall_cons_1 _ _ _ HF) as [Hx Hl].
  rewrite filter_cons. case_decide; [| contradiction]. by rewrite (IH Hl).
Qed.

(* the three byte-valued disjuncts, at one disciplined byte *)
Lemma disc_drop_byte (I : list (bv 8)) (c : bv 8) :
  disc_input I -> c ∈ I ->
  bv_unsigned c <> 0%Z /\ bv_unsigned c <> 16%Z /\ cons_erase c = false.
Proof.
  intros Hd Hc. pose proof (disc_input_byte_val I c Hd Hc) as Hv.
  split; [lia |]. split; [lia |]. apply (disc_byte_ok I c Hd Hc).
Qed.

(* THE FULL-RING DISJUNCT.  [L] is the era's log at the moment the arm
   opens, [dl] what the claim has delivered, [Eb] the bytes the claim has
   echoed and [w] the process output it still owes. *)
Lemma drop_refuted (h : list mobs) (L : list log_entry)
      (dl : list (list mobs * bv 8)) (Eb w : list (bv 8)) :
  (length L + 1)%nat = length (ins (open_seg h)) ->
  Forall log_echoed L ->
  (128 + length dl <= length (filter log_echoed L))%nat ->
  (lines_bytes Eb (if decide (rest_of Eb = [] /\ w = [])
                   then (nlines Eb - 1)%nat else nlines Eb)
   <= length dl)%nat ->
  Eb = take (length L) (ins (open_seg h)) ->
  disc_input (ins (open_seg h)) ->
  False.
Proof.
  intros HK1 HA1 Hring HA2 HEb Hdisc.
  rewrite (epu_filter_all log_echoed L HA1) in Hring.
  assert (HlenEb : length Eb = length L)
    by (rewrite HEb length_take; lia).
  assert (HdEb : disc_input Eb)
    by (rewrite HEb; exact (disc_input_prefix _ _ (prefix_take _ _) Hdisc)).
  assert (Hb : (length Eb
                <= lines_bytes Eb (if decide (rest_of Eb = [] /\ w = [])
                                   then (nlines Eb - 1)%nat else nlines Eb)
                   + line_max)%nat).
  { apply (lines_bytes_disc_bound Eb _ HdEb). case_decide as Hc.
    - right. split; [exact (proj1 Hc) | reflexivity].
    - by left. }
  rewrite /line_max in Hb. lia.
Qed.

(* ...and the two together, at the shape [ConsLog.cons_ev_ok] hands the
   claim at [EvOpen] *)
Lemma cons_drop_refuted (h : list mobs) (c : bv 8) (L : list log_entry)
      (dl : list (list mobs * bv 8)) (Eb w : list (bv 8)) :
  (length L + 1)%nat = length (ins (open_seg h)) ->
  Forall log_echoed L ->
  (lines_bytes Eb (if decide (rest_of Eb = [] /\ w = [])
                   then (nlines Eb - 1)%nat else nlines Eb)
   <= length dl)%nat ->
  Eb = take (length L) (ins (open_seg h)) ->
  disc_input (ins (open_seg h)) ->
  c ∈ ins (open_seg h) ->
  cons_drop_ok c L dl -> False.
Proof.
  intros HK1 HA1 HA2 HEb Hdisc Hc Hdrop.
  destruct (disc_drop_byte _ c Hdisc Hc) as (H0 & H16 & Her).
  destruct Hdrop as [Hz | [Hp | [He | Hring]]].
  - exact (H0 Hz).
  - exact (H16 Hp).
  - rewrite Her in He. discriminate.
  - exact (drop_refuted h L dl Eb w HK1 HA1 Hring HA2 HEb Hdisc).
Qed.

(* ====================================================================== *)
(*  6.  F3 -- THE READ WINDOW IS A SLICE OF [E]                            *)
(* ====================================================================== *)

(* the entries a read may hand out: the ECHOED ones, in log order *)
Definition echoed (pops : list log_entry) : list (list mobs * bv 8) :=
  (fun e => (le_hist e, le_byte e)) <$> filter log_echoed pops.

Lemma echoed_lookup (pops : list log_entry) (j : nat) (x : list mobs * bv 8) :
  echoed pops !! j = Some x ->
  exists e, e ∈ pops /\ log_echoed e /\ (le_hist e, le_byte e) = x.
Proof.
  rewrite /echoed list_lookup_fmap fmap_Some.
  intros (e & He & ->). exists e. split; [|split; [|reflexivity]].
  - apply list_elem_of_lookup_2 in He. by apply list_elem_of_filter in He as [_ ?].
  - apply list_elem_of_lookup_2 in He. by apply list_elem_of_filter in He as [? _].
Qed.

Lemma echoed_elem (pops : list log_entry) (e : log_entry) :
  e ∈ pops -> log_echoed e -> (le_hist e, le_byte e) ∈ echoed pops.
Proof.
  intros Hin Hec. rewrite /echoed. apply list_elem_of_fmap.
  exists e. split; [reflexivity|]. by apply list_elem_of_filter.
Qed.

(* A FILTER KEEPS A STRICT ORDER ON THE INDICES.  The general step behind
   "[echoed pops] is history-ordered because [pops] is". *)
Lemma epu_filter_cons_T {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (a : A) (l : list A) : P a -> filter P (a :: l) = a :: filter P l.
Proof. intro Hp. rewrite filter_cons. case_decide; [done|contradiction]. Qed.

Lemma epu_filter_cons_F {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (a : A) (l : list A) : ~ P a -> filter P (a :: l) = filter P l.
Proof. intro Hp. rewrite filter_cons. case_decide; [contradiction|done]. Qed.

Lemma filter_strict_order {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (R : A -> A -> Prop) (l : list A) :
  (forall i j x y, i < j -> l !! i = Some x -> l !! j = Some y -> R x y) ->
  (forall i j x y, i < j -> filter P l !! i = Some x ->
                   filter P l !! j = Some y -> R x y).
Proof.
  induction l as [|a l IH]; intros Hl i j x y Hij Hx Hy.
  { rewrite filter_nil in Hx. by rewrite lookup_nil in Hx. }
  assert (Hl' : forall i j x y, i < j -> l !! i = Some x -> l !! j = Some y -> R x y).
  { intros i' j' x' y' Hij' Hx' Hy'. by eapply (Hl (S i') (S j')); [lia| |]. }
  destruct (decide (P a)) as [Hpa|Hpa].
  - rewrite (epu_filter_cons_T P a l Hpa) in Hx, Hy.
    destruct i as [|i].
    + cbn in Hx. simplify_eq.
      destruct j as [|j]; [lia|]. cbn in Hy.
      assert (Hin : y ∈ l).
      { apply list_elem_of_lookup_2 in Hy.
        by apply list_elem_of_filter in Hy as [_ ?]. }
      apply list_elem_of_lookup in Hin as [n Hn].
      by eapply (Hl 0%nat (S n)); [lia| |].
    + destruct j as [|j]; [lia|]. cbn in Hx, Hy.
      apply (IH Hl' i j x y); [lia|exact Hx|exact Hy].
  - rewrite (epu_filter_cons_F P a l Hpa) in Hx, Hy.
    by eapply IH; [exact Hl'|exact Hij| |].
Qed.

Lemma echoed_order (pops : list log_entry) (i j : nat)
      (x y : list mobs * bv 8) :
  log_ok pops -> i < j ->
  echoed pops !! i = Some x -> echoed pops !! j = Some y ->
  hist_ext x.1 y.1.
Proof.
  intros Hlog Hij Hx Hy.
  rewrite /echoed list_lookup_fmap fmap_Some in Hx.
  destruct Hx as (e1 & He1 & ->).
  rewrite /echoed list_lookup_fmap fmap_Some in Hy.
  destruct Hy as (e2 & He2 & ->). cbn.
  eapply (filter_strict_order log_echoed
            (fun a b => hist_ext (le_hist a) (le_hist b)) pops);
    [ |exact Hij|exact He1|exact He2].
  intros i' j' a b Hij' Ha Hb. by eapply log_ok_lt.
Qed.

(* ---- what refutes an entry in a gap ---- *)

Lemma hist_ext_nil_of_ends (h : list mobs) (c : bv 8) :
  obs_ends_in Uart0 h c -> hist_ext [] h.
Proof.
  intros [h0 ->]. split; [apply prefix_nil|]. rewrite length_app /=. lia.
Qed.

Lemma echoed_elem_inv (pops : list log_entry) (y : list mobs * bv 8) :
  y ∈ echoed pops ->
  exists e, e ∈ pops /\ log_echoed e /\ (le_hist e, le_byte e) = y.
Proof.
  rewrite /echoed. intros Hy. apply list_elem_of_fmap in Hy as (e & -> & He).
  apply list_elem_of_filter in He as [Hec Hin]. by exists e.
Qed.

(* NO LOGGED BYTE IS AN ERASE CHARACTER, under the discipline -- which
   kills the gap clause's second disjunct outright *)
Lemma pops_no_erase (pops : list log_entry) :
  log_ok pops -> (forall e, e ∈ pops -> disc_seg (le_hist e)) ->
  forall e, e ∈ pops -> cons_erase (le_byte e) = false.
Proof.
  intros [Hends _] Hdisc e He.
  eapply disc_seg_no_erase; [by apply Hdisc|by apply (proj1 (Hends e He))].
Qed.

(* ...so NO ECHOED ENTRY LIES STRICTLY INSIDE A GAP *)
(* ...SO NO ECHOED ENTRY LIES STRICTLY INSIDE A GAP.  The premise is the ONE
   consequence of the discipline this argument uses -- [pops_no_erase] is its
   producer -- and not the discipline itself: lane ECHO-OUT's claim carries
   the discipline of each entry's CYCLE SEGMENT, from which the whole
   history's [disc_seg] does not follow, while the no-erase fact does
   ([disc_seg_no_erase] at the segment). *)
Lemma no_echoed_between (pops : list log_entry) (h1 h2 : list mobs)
      (y : list mobs * bv 8) :
  log_ok pops -> (forall e, e ∈ pops -> cons_erase (le_byte e) = false) ->
  gap_ok pops h1 h2 ->
  y ∈ echoed pops -> hist_ext h1 y.1 -> hist_ext y.1 h2 -> False.
Proof.
  intros Hlog Hnoer Hgap Hy H1 H2.
  destruct (echoed_elem_inv pops y Hy) as (e & Hein & Hech & Heq).
  assert (Hh : le_hist e = y.1) by (by rewrite -Heq).
  destruct Hgap as [Hleft|(e' & He'in & _ & _ & Herase)].
  - apply (log_echoed_nonnil e Hech). apply (Hleft e Hein); by rewrite Hh.
  - rewrite (Hnoer e' He'in) in Herase. discriminate.
Qed.

(* F3(a): THE CONSUMED INPUTS ARE AN INITIAL SEGMENT OF THE ECHOED ONES.

   [ws] is the window the read path CONSUMED, not the window it delivered:
   the kernel has two exits that pop a byte and hand it to nobody (a
   leading ^D, and a copy-out fault), so the delivered bytes are a PREFIX
   of [ws] of some length [d].  F3(a) is about the consumed window, which
   is the one [read_ok] speaks of; the swallow is refuted separately (a
   disciplined byte is never ^D: [disc_seg_no_ctrl_d]).

   THE LOG-TO-[E] IDENTIFICATION LIVES HERE AND ONLY HERE.  F1 and F2 are
   stated over an abstract [E] on purpose: the kernel appends the log entry
   AFTER the echo's out_links, so between the two the claim's [E] is one
   entry AHEAD of [echoed pops] and no lemma may assume they agree.

   HYPOTHESES THE NOTE DOES NOT LIST.  (1) The no-erase fact is needed for
   EVERY entry of [pops], not only for [ws]'s: the gap clause's erase
   disjunct names an arbitrary LOG entry, which need not have been consumed,
   and the only thing that refutes it is that a disciplined input byte is a
   body byte or a newline and no erase byte is either.  It is the DISCIPLINE'S
   consequence and not the discipline ([pops_no_erase] is the producer, and
   [disc_seg_no_erase] is it at a cycle segment, which is the form lane
   ECHO-OUT's claim carries).  (2) [log_ok pops]
   is what makes [echoed pops] history-ordered, so that "no log entry
   strictly between two consecutive consumed ones" is a statement about
   INDICES.  Both hold on the Iris side -- [disc] is prefix-closed, so
   every history in the log is disciplined once the current one is -- but
   neither is in the note's list. *)
Lemma read_window_prefix (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) :
  log_ok pops ->
  read_ok pops dl ws ->
  (forall e, e ∈ pops -> cons_erase (le_byte e) = false) ->
  dl `prefix_of` echoed pops ->
  (dl ++ ws) `prefix_of` echoed pops.
Proof.
  intros Hlog (Hin & Hchain & Hgap0 & Hgap) Hnoer Hdl.
  (* the consumed list agrees with [echoed pops] index by index, by strong
     induction on the index (the bound [N] is the induction's measure) *)
  assert (Hpt : forall N k, k < N -> k < length (dl ++ ws) ->
                  echoed pops !! k = (dl ++ ws) !! k).
  { induction N as [|N IHN]; intros k HkN Hk; [lia|].
    destruct ((dl ++ ws) !! k) as [p|] eqn:Hp;
      [|exfalso; apply lookup_ge_None_1 in Hp; lia].
    destruct (decide (k < length dl)) as [Hkl|Hkl].
    { (* below [dl]: [dl] is already an initial segment *)
      destruct Hdl as [z Hz]. rewrite Hz.
      rewrite lookup_app_l; last exact Hkl.
      rewrite lookup_app_l in Hp; last exact Hkl. exact Hp. }
    (* at or above [dl]: [p] is an entry of [ws], hence an echoed entry *)
    assert (Hpin : p ∈ ws).
    { rewrite lookup_app_r in Hp; [|lia]. by eapply list_elem_of_lookup_2. }
    destruct (Hin p Hpin) as (ep & Hepin & Hepeq & Hepech).
    assert (HpE : p ∈ echoed pops).
    { rewrite -Hepeq. by apply echoed_elem. }
    apply list_elem_of_lookup in HpE as [n Hn].
    assert (Hnk : n = k).
    { destruct (decide (n < k)) as [Hlt|Hge].
      - (* the same entry twice in the consumed list: the chain forbids it *)
        exfalso. rewrite (IHN n ltac:(lia) ltac:(lia)) in Hn.
        destruct p as [hp cp].
        eapply hist_ext_irrefl, (hist_chain_lt _ n k); [exact Hchain|lia| |];
          [exact Hn|exact Hp].
      - destruct (decide (k < n)) as [Hlt|?]; [|lia]. exfalso.
        (* an echoed entry sits strictly inside the gap the read left *)
        assert (Hy : is_Some (echoed pops !! k)).
        { apply lookup_lt_is_Some. apply lookup_lt_Some in Hn. lia. }
        destruct Hy as [y Hy].
        assert (Hyp : hist_ext y.1 p.1)
          by (eapply echoed_order; [exact Hlog|exact Hlt|exact Hy|exact Hn]).
        assert (HyE : y ∈ echoed pops) by (by eapply list_elem_of_lookup_2).
        destruct k as [|k'].
        + destruct p as [hp cp].
          eapply (no_echoed_between pops [] hp y);
            [exact Hlog|exact Hnoer|by eapply Hgap0|exact HyE| |exact Hyp].
          destruct (echoed_elem_inv pops y HyE) as (ey & Heyin & _ & Heyeq).
          rewrite -Heyeq /=.
          eapply hist_ext_nil_of_ends.
          by apply (proj1 (proj1 Hlog ey Heyin)).
        + assert (Hp' : is_Some ((dl ++ ws) !! k')) by (apply lookup_lt_is_Some; lia).
          destruct Hp' as [p' Hp'].
          assert (HE' : echoed pops !! k' = Some p')
            by (rewrite (IHN k' ltac:(lia) ltac:(lia)); exact Hp').
          destruct p as [hp cp]. destruct p' as [hp' cp'].
          eapply (no_echoed_between pops hp' hp y);
            [exact Hlog|exact Hnoer|by eapply Hgap|exact HyE| |exact Hyp].
          apply (echoed_order pops k' (S k') (hp', cp') y);
            [exact Hlog|lia|exact HE'|exact Hy]. }
    by rewrite Hnk in Hn. }
  (* pointwise agreement over the whole consumed list IS the prefix *)
  assert (Hle : length (dl ++ ws) <= length (echoed pops)).
  { destruct (decide (length (dl ++ ws) = 0)) as [H0|Hne]; [lia|].
    destruct ((dl ++ ws) !! (length (dl ++ ws) - 1)) as [p|] eqn:Hp;
      [|apply lookup_ge_None_1 in Hp; lia].
    pose proof (Hpt (length (dl ++ ws)) (length (dl ++ ws) - 1)
                  ltac:(lia) ltac:(lia)) as Hq.
    rewrite Hp in Hq. apply lookup_lt_Some in Hq. lia. }
  assert (Heq : take (length (dl ++ ws)) (echoed pops) = dl ++ ws).
  { apply list_eq. intros k.
    destruct (decide (k < length (dl ++ ws))) as [Hk|Hk].
    - rewrite lookup_take_lt; [|exact Hk]. by eapply (Hpt (S k)); [lia|].
    - rewrite lookup_take_ge; [|lia]. symmetry. apply lookup_ge_None_2. lia. }
  exists (drop (length (dl ++ ws)) (echoed pops)).
  by rewrite -{1}(take_drop (length (dl ++ ws)) (echoed pops)) Heq.
Qed.

(* ====================================================================== *)
(*  7.  F4 -- PHI's PURE PART                                              *)
(* ====================================================================== *)

(* THE CLAIM GIVES [good_out] AT THE SEGMENT.  [Forall (< 4) cs] is needed
   HERE and not in F1 -- [expected_rel] quantifies over a BOUNDED choice
   list, while [D] and [sess] index [cs] with the same total [!!!] and
   agree out of range.  [length cs = nlines] is not needed at all, for the
   same reason.  The input premise is a PREFIX and not a length, because
   [EchoDisc.sess_mono] is stated at the input. *)
Lemma good_out_of_stage (ps cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) (seg : list mobs) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  Forall (fun i => (i < 4)%nat) cs ->
  E_disc E ->
  pro_pin ps cs (snd <$> E) ->
  w `prefix_of` pending ps cs E ->
  obs_wire Uart0 seg `prefix_of` (D ps cs E ++ w) ->
  (snd <$> E) `prefix_of` ins seg ->
  good_out seg.
Proof.
  intros Hps Hcs HE Hpin Hw Hwire Hinp.
  (* THE WITNESS IS THE STAGE'S RESOLUTION PADDED WITH ONE TERMINATED ROUND:
     the stage may be standing mid-prologue, and [expected_rel] quantifies
     over a SETTLED one.  Padding moves no round the stage has read. *)
  set (ps' := (ps ++ replicate (S (nlines (ins seg))) 0%nat)%list).
  assert (Hpp : ps `prefix_of` ps') by (rewrite /ps'; by eexists).
  exists ps', cs. split.
  { apply pro_ok_pad; [exact Hps | lia]. }
  split; [exact Hcs |].
  etrans; [exact Hwire |].
  rewrite (D_ps_ext ps ps' cs E Hpp Hpin).
  etrans; [| by apply (sess_mono ps' cs (snd <$> E) (ins seg))].
  apply (D_stage_prefix ps' cs E w HE).
  etrans; [exact Hw |]. by apply pending_ps_mono.
Qed.

(* WHAT IS NO LONGER HERE: [echo_phi_of_good_out], the weakening from
   [Forall good_out (cycles_of h)] to the PER-CYCLE GUARDED form
   [Forall (fun seg => disc_seg' seg -> good_out seg) (cycles_of h)].
   [AppEcho.echo_phi] WAS that guarded form; since lane ECHO-OUT part 5 it
   is the owner's WHOLE-HISTORY implication [disc h -> Forall good_out
   (cycles_of h)] ("there is no per-cycle form -- once we get taint in one
   era, it's tainted forever"), which the ledger pays directly
   ([EchoOut.echo_led_phi]).  Nothing bridges to the guarded shape any
   more, and nothing ever used this lemma. *)

(* ====================================================================== *)
(*  8.  THE TWO WITNESSES PUT THE SAME BYTES ON THE WIRE                   *)
(*                                                                        *)
(*  Lane ECHO-OUT needs D1's LOWER bound at the CLAIM's resolution, and    *)
(*  the discipline supplies it at ITS OWN existential witness              *)
(*  ([EchoDisc.disc_seg'] is [∃ ps cs, ... disc_pt ps cs p]).  The two     *)
(*  pairs are different objects, and F2 is stated at one pair on purpose.  *)
(*                                                                        *)
(*  WHAT REPLACES PREFIX-FREENESS.  With the line fixed the four line      *)
(*  alternatives began with 'h', 'e', '$', 'f' and the resolution was      *)
(*  readable off one byte of the wire.  At an arbitrary line that fails,   *)
(*  and the owner's ruling of 2026-09-16 ADMITS the two lines at which it  *)
(*  fails: [echo fork] prints "fork\n$ ", which is sh's panic line         *)
(*  followed by a bare prompt, and [echo exec echo failed] prints sh's     *)
(*  exec diagnostic.  So nothing below concludes that two witnesses agree  *)
(*  on an INDEX.  What it concludes is that they put the SAME BYTES on the *)
(*  wire, which is all the claim ever needed and which holds at every      *)
(*  line ([sess_prefix_det]).                                             *)
(* ====================================================================== *)

(* out of range [!!!] reads [0], which IS in range, so this is the honest
   hypothesis and it follows from the [Forall] both sides carry *)
Definition cs_ok (cs : list nat) : Prop := forall i, (cs !!! i < 4)%nat.

Lemma cs_ok_of_Forall cs : Forall (fun x => (x < 4)%nat) cs -> cs_ok cs.
Proof.
  intros HF i. destruct (decide (i < length cs)%nat) as [Hi | Hi].
  - destruct (lookup_lt_is_Some_2 cs i Hi) as [x Hx].
    rewrite (list_lookup_total_correct cs i x Hx).
    exact (Forall_lookup_1 _ _ _ _ HF Hx).
  - rewrite list_lookup_total_alt (lookup_ge_None_2 cs i ltac:(lia)) /=. lia.
Qed.

Lemma lookup_total_drop {A} `{!Inhabited A} (n i : nat) (l : list A) :
  drop n l !!! i = l !!! (n + i).
Proof. by rewrite !list_lookup_total_alt lookup_drop. Qed.

Lemma cs_ok_drop cs n : cs_ok cs -> cs_ok (drop n cs).
Proof. intros H i. rewrite lookup_total_drop. apply H. Qed.

(* THE ROUND POINTER MOVES WITH THE DROP: dropping [n] lines drops the
   [pro_idx cs n] prologue rounds those lines opened. *)
Lemma pro_idx_add cs n i :
  pro_idx cs (n + i) = (pro_idx cs n + pro_idx (drop n cs) i)%nat.
Proof.
  induction i as [| i IH]; [rewrite Nat.add_0_r; cbn [pro_idx]; lia |].
  rewrite Nat.add_succ_r !pro_idx_S IH lookup_total_drop.
  case_decide; lia.
Qed.

Lemma alt_cont_drop ps cs bs n i :
  alt_cont (pro_from (pro_idx cs n) ps) (drop n cs) (drop n bs) i
  = alt_cont ps cs bs (n + i).
Proof.
  rewrite /alt_cont !lookup_total_drop. f_equal.
  case_decide as H3; [| done].
  rewrite pro_from_add pro_idx_add. f_equal. f_equal. lia.
Qed.

Lemma alt_blk_drop ps cs bs n i :
  alt_blk (pro_from (pro_idx cs n) ps) (drop n cs) (drop n bs) i
  = alt_blk ps cs bs (n + i).
Proof. by rewrite /alt_blk lookup_total_drop alt_cont_drop. Qed.

Lemma alt_seq_cons ps cs bs q :
  alt_seq ps cs bs (S q)
  = alt_blk ps cs bs 0%nat
    ++ alt_seq (pro_from (pro_idx cs 1%nat) ps) (drop 1 cs) (drop 1 bs) q.
Proof.
  rewrite /alt_seq.
  replace (List.seq 0 (S q)) with (0%nat :: List.seq 1 q) by reflexivity.
  rewrite fmap_cons concat_cons. f_equal.
  rewrite -List.seq_shift -list_fmap_compose.
  f_equal. apply list_fmap_ext.
  intros i x Hx. rewrite /compose. by rewrite (alt_blk_drop ps cs bs 1 x).
Qed.

(* the reassociation the induction consumes: a block sequence and whatever
   follows it is the first body, its newline, and the rest *)
Lemma epu_app4 {A} (a c s t : list A) (n : A) :
  ((a ++ n :: c) ++ s) ++ t = a ++ n :: (c ++ (s ++ t)).
Proof. by rewrite -!app_assoc. Qed.

Lemma alt_seq_cons_assoc ps cs bs q (t : list (bv 8)) :
  alt_seq ps cs bs (S q) ++ t
  = bs !!! 0%nat
    ++ wl_nl :: (alt_cont ps cs bs 0%nat
                 ++ (alt_seq (pro_from (pro_idx cs 1%nat) ps) (drop 1 cs)
                       (drop 1 bs) q ++ t)).
Proof. rewrite alt_seq_cons /alt_blk. apply epu_app4. Qed.

(* the two readings of a list total lookup the induction needs, both under
   a bound so that the out-of-range inhabitant never arises *)
Lemma nonl_lta (bs : list (list (bv 8))) (i : nat) :
  Forall (fun l => wl_nl ∉ l) bs -> (i < length bs)%nat -> wl_nl ∉ bs !!! i.
Proof.
  intros HF Hi. destruct (lookup_lt_is_Some_2 bs i Hi) as [l Hl].
  rewrite (list_lookup_total_correct bs i l Hl).
  exact (Forall_lookup_1 _ _ _ _ HF Hl).
Qed.

Lemma wf_lta (bs : list (list (bv 8))) (q i : nat) :
  Forall (fun l => wl_wf (drop 1 (wl_words l))) (take q bs) ->
  (i < q)%nat -> (q <= length bs)%nat ->
  wl_wf (drop 1 (wl_words (bs !!! i))).
Proof.
  intros HF Hi Hq.
  destruct (lookup_lt_is_Some_2 bs i ltac:(lia)) as [l Hl].
  rewrite (list_lookup_total_correct bs i l Hl).
  assert (Htk : take q bs !! i = Some l)
    by (rewrite lookup_take_lt; [exact Hl | exact Hi]).
  exact (Forall_lookup_1 (fun l0 => wl_wf (drop 1 (wl_words l0)))
           (take q bs) i l HF Htk).
Qed.

Lemma epu_take_S {A} `{!Inhabited A} (n : nat) (l : list A) :
  (S n <= length l)%nat -> take (S n) l = l !!! 0%nat :: take n (drop 1 l).
Proof.
  destruct l as [| a l]; [cbn [length]; lia |].
  intros _. cbn [take drop]. by rewrite list_lookup_total_alt /=.
Qed.

Lemma lta_of_take_eq (bs bs' : list (list (bv 8))) (q j : nat) :
  take q bs' = take q bs -> (j < q)%nat -> bs' !!! j = bs !!! j.
Proof.
  intros Heq Hj.
  assert (H1 : bs' !! j = take q bs' !! j)
    by (symmetry; rewrite lookup_take_lt; [done | lia]).
  assert (H2 : bs !! j = take q bs !! j)
    by (symmetry; rewrite lookup_take_lt; [done | lia]).
  by rewrite !list_lookup_total_alt H1 H2 Heq.
Qed.

(* A SETTLED PROLOGUE WHOSE FIRST BYTE IS '$' IS THE BARE PROMPT: letter 0
   is the only one that opens on '$', and it ENDS the round, so nothing
   follows it.  This is what the two collisions come down to. *)
Lemma epu_prompt_of_dollar (P : list nat) (X Y : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) P -> pro_done P ->
  (u_prompt ++ Y) `prefix_of` (pro_of P ++ X) ->
  pro_of P = u_prompt.
Proof.
  intros HF Hd Hp.
  assert (Hne : P <> []) by (intros ->; by apply Exists_nil in Hd).
  pose proof (pro_of_pos P HF Hne) as Hpos.
  apply (pro_of_dollar_prompt P HF Hne). intros b Hb.
  assert (H1 : (u_prompt ++ Y) !! 0%nat = Some (Z_to_bv 8 36%Z))
    by (rewrite lookup_app_l; [exact u_prompt_head | exact u_prompt_pos]).
  assert (H2 : (pro_of P ++ X) !! 0%nat = Some (Z_to_bv 8 36%Z))
    by (eapply prefix_lookup_Some; [exact H1 | exact Hp]).
  rewrite (lookup_app_l (pro_of P) X 0%nat Hpos) Hb in H2.
  injection H2 as H2. rewrite H2. by vm_compute.
Qed.

(* THE BLOCK STEP: two continuations below ONE wire are the SAME BYTES, and
   the unprimed round is settled.  It does NOT conclude that the two chose
   the same alternative -- that is false at the two collisions
   ([EchoDisc.line_alts_of_prefix_bytes]) -- and it does not need
   prefix-freeness anywhere.  The case table:
     - same index, not 3: equal lists, [X' ⊑ X].
     - same index 3: two prologues below one wire; the primed one is
       settled by premise, so [pro_of_prefix_free] settles the unprimed one
       and the bytes agree.
     - the alt0/alt1 collision: the two alternatives are the same list.
     - alt0 (primed) against alt3 (unprimed) at [drop 1 ws = dg_fork]: the
       wire shows "fork\n$ " on the left, so the unprimed round's prologue
       has to start with '$'.  An OPEN prologue is empty or starts with 'i'
       ([pro_of_open_head]), so the round is settled -- by the caller's
       premise when anything follows the block, and by the hypothesis
       itself when nothing does -- and a settled prologue starting with '$'
       IS the bare prompt.  Same bytes.
     - alt3 (primed) against alt0 (unprimed): the mirror, with the primed
       round settled by premise.
     - every other pair: incomparable. *)
Lemma alt_cont_prefix_det (ps ps' cs cs' : list nat)
    (bs : list (list (bv 8))) (X X' : list (bv 8)) :
  cs_ok cs -> cs_ok cs' ->
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  Forall (fun a => (a < length pro_alts)%nat) ps' ->
  wl_wf (drop 1 (wl_words (bs !!! 0%nat))) ->
  (cs' !!! 0%nat = 3%nat -> (1 < pro_rounds ps')%nat) ->
  (cs !!! 0%nat = 3%nat -> X <> [] -> (1 < pro_rounds ps)%nat) ->
  (alt_cont ps' cs' bs 0%nat ++ X') `prefix_of` (alt_cont ps cs bs 0%nat ++ X) ->
  (cs !!! 0%nat = 3%nat -> (1 < pro_rounds ps)%nat)
  /\ alt_cont ps' cs' bs 0%nat = alt_cont ps cs bs 0%nat
  /\ X' `prefix_of` X.
Proof.
  intros Hcs Hcs' Hps Hps' Hwf Hset' Hset Hp.
  rewrite /alt_cont in Hp |- *.
  replace (S (pro_idx cs 0%nat)) with 1%nat in Hp |- * by reflexivity.
  replace (S (pro_idx cs' 0%nat)) with 1%nat in Hp |- * by reflexivity.
  rewrite -(app_assoc (line_alts_of (wl_words (bs !!! 0%nat)) !!! (cs' !!! 0%nat))
              _ X')
          -(app_assoc (line_alts_of (wl_words (bs !!! 0%nat)) !!! (cs !!! 0%nat))
              _ X) in Hp.
  destruct (line_alts_of_prefix_bytes (wl_words (bs !!! 0%nat))
              (cs' !!! 0%nat) (cs !!! 0%nat) _ _ Hwf (Hcs' 0%nat) (Hcs 0%nat) Hp)
    as [Heq | [(Ha3 & Hb3 & Hlt) | [(Ha0 & Hb3 & Hfk) | (Ha3 & Hb0 & Hfk)]]].
  - (* SAME ALTERNATIVE *)
    rewrite Heq in Hp |- *. apply prefix_app_inv in Hp.
    (* [destruct] on the decision resolves every copy of the [if], in the
       goal and in [Hp] alike *)
    destruct (decide (cs !!! 0%nat = 3%nat)) as [H3 | H3]; last first.
    { split; [intros Hq; by destruct (H3 Hq) |].
      split; [reflexivity | exact Hp]. }
    assert (Hd' : pro_done (pro_from 1%nat ps')).
    { apply pro_from_done. apply Hset'. by rewrite Heq. }
    pose proof (pro_from_Forall _ 1%nat ps Hps) as HFA.
    pose proof (pro_from_Forall _ 1%nat ps' Hps') as HFB.
    assert (Hcmp : pro_of (pro_from 1%nat ps')
                   `prefix_of` pro_of (pro_from 1%nat ps)).
    { destruct (decide (X = [])) as [HX0 | HXne].
      - rewrite HX0 app_nil_r in Hp.
        etrans; [apply prefix_app_r; reflexivity | exact Hp].
      - assert (HdA : pro_done (pro_from 1%nat ps))
          by (apply pro_from_done, Hset; [exact H3 | exact HXne]).
        destruct (prefix_weak_total (pro_of (pro_from 1%nat ps'))
                    (pro_of (pro_from 1%nat ps))
                    (pro_of (pro_from 1%nat ps) ++ X)
                    ltac:(etrans; [apply prefix_app_r; reflexivity | exact Hp])
                    ltac:(apply prefix_app_r; reflexivity)) as [H | H];
          [exact H |].
        destruct (pro_of_prefix_free (pro_from 1%nat ps') (pro_from 1%nat ps)
                    HFB HFA HdA H) as [_ Heqp]. by rewrite Heqp. }
    destruct (pro_of_prefix_free (pro_from 1%nat ps) (pro_from 1%nat ps')
                HFA HFB Hd' Hcmp) as [HdA Heqp].
    rewrite Heqp in Hp. apply prefix_app_inv in Hp.
    split; [intros _; by apply pro_from_done |].
    split; [by rewrite Heqp | exact Hp].
  - (* THE alt0/alt1 COLLISION: the two alternatives are the same list *)
    rewrite (decide_False _ _ Ha3) (decide_False _ _ Hb3) in Hp |- *.
    rewrite !app_nil_l Hlt in Hp. apply prefix_app_inv in Hp.
    split; [intros Hq; by destruct (Hb3 Hq) |].
    split; [by rewrite Hlt | exact Hp].
  - (* THE PRIMED SIDE ECHOED [fork]; THE UNPRIMED SIDE PANICKED *)
    assert (Ha3' : cs' !!! 0%nat <> 3%nat) by (rewrite Ha0; discriminate).
    rewrite (decide_False _ _ Ha3') (decide_True _ _ Hb3) in Hp |- *.
    rewrite Ha0 Hb3 (line_alts_of_fork _ Hfk) line_alts_of_3 in Hp |- *.
    rewrite !app_nil_l -(app_assoc alt_panic u_prompt X') in Hp.
    apply prefix_app_inv in Hp.
    assert (HdA : pro_done (pro_from 1%nat ps)).
    { destruct (decide (pro_done (pro_from 1%nat ps))) as [Hy | Hopen];
        [exact Hy | exfalso].
      destruct (decide (X = [])) as [HX0 | HXne]; last first.
      { apply Hopen, pro_from_done, Hset; [exact Hb3 | exact HXne]. }
      rewrite HX0 app_nil_r in Hp.
      assert (Hpos : (0 < length (pro_of (pro_from 1%nat ps)))%nat).
      { pose proof (prefix_length _ _ Hp) as Hl.
        rewrite (length_app u_prompt X') in Hl.
        pose proof u_prompt_pos. lia. }
      assert (H1 : (u_prompt ++ X') !! 0%nat = Some (Z_to_bv 8 36%Z))
        by (rewrite lookup_app_l; [exact u_prompt_head | exact u_prompt_pos]).
      assert (H2 : pro_of (pro_from 1%nat ps) !! 0%nat
                   = Some (Z_to_bv 8 36%Z))
        by (eapply prefix_lookup_Some; [exact H1 | exact Hp]).
      pose proof (pro_of_open_head (pro_from 1%nat ps) (Z_to_bv 8 36%Z)
                    Hopen H2) as Hv.
      rewrite (_ : bv_unsigned (Z_to_bv 8 36%Z) = 36%Z) in Hv;
        [lia | by vm_compute]. }
    assert (Heqp : pro_of (pro_from 1%nat ps) = u_prompt)
      by (apply (epu_prompt_of_dollar (pro_from 1%nat ps) X X');
          [exact (pro_from_Forall _ 1%nat ps Hps) | exact HdA | exact Hp]).
    rewrite Heqp in Hp. apply prefix_app_inv in Hp.
    split; [intros _; by apply pro_from_done |].
    split; [| exact Hp]. by rewrite Heqp app_nil_r.
  - (* THE MIRROR: the primed side panicked, the unprimed echoed [fork] *)
    assert (Hb3' : cs !!! 0%nat <> 3%nat) by (rewrite Hb0; discriminate).
    rewrite (decide_True _ _ Ha3) (decide_False _ _ Hb3') in Hp |- *.
    rewrite Ha3 Hb0 (line_alts_of_fork _ Hfk) line_alts_of_3 in Hp |- *.
    rewrite !app_nil_l -(app_assoc alt_panic u_prompt X) in Hp.
    apply prefix_app_inv in Hp.
    assert (Hd' : pro_done (pro_from 1%nat ps'))
      by (apply pro_from_done, Hset'; exact Ha3).
    assert (Hne' : pro_from 1%nat ps' <> [])
      by (intros Hz; rewrite Hz in Hd'; by apply Exists_nil in Hd').
    assert (Heqp : pro_of (pro_from 1%nat ps') = u_prompt).
    { apply (pro_of_dollar_prompt (pro_from 1%nat ps')
               (pro_from_Forall _ 1%nat ps' Hps') Hne').
      intros b Hb.
      assert (H2 : (u_prompt ++ X) !! 0%nat = Some b).
      { eapply prefix_lookup_Some; [| exact Hp].
        rewrite lookup_app_l; [exact Hb |].
        apply lookup_lt_Some in Hb. lia. }
      rewrite (lookup_app_l u_prompt X 0%nat u_prompt_pos) u_prompt_head in H2.
      injection H2 as H2. rewrite -H2. by vm_compute. }
    rewrite Heqp in Hp. apply prefix_app_inv in Hp.
    split; [intros Hq; discriminate |].
    split; [| exact Hp]. by rewrite Heqp app_nil_r.
Qed.

(* THE STEP: two block sequences below one wire have the same BODIES and
   the same BYTES.  The old conclusion "[cs'] agrees with [cs] below [q']"
   is GONE -- the two collisions make it false -- and what replaces it for
   the consumer is the third conjunct, that the machine's round for block
   [q'] has settled.  The premises for the unprimed side are [pro_pin]'s
   reading: every block strictly below [q] is settled, and block [q] is
   settled if anything follows it. *)
Lemma alt_seq_prefix_det (q' : nat) :
  forall (ps ps' cs cs' : list nat) (bs bs' : list (list (bv 8)))
         (q : nat) (t' t : list (bv 8)),
    Forall (fun a => (a < length pro_alts)%nat) ps ->
    Forall (fun a => (a < length pro_alts)%nat) ps' ->
    (pro_idx cs' q' < pro_rounds ps')%nat ->
    (0 < pro_rounds ps)%nat ->
    (forall i, (i < q)%nat -> (pro_idx cs i < pro_rounds ps)%nat) ->
    (t <> [] -> (pro_idx cs q < pro_rounds ps)%nat) ->
    cs_ok cs -> cs_ok cs' ->
    (q' <= length bs')%nat -> (q <= length bs)%nat ->
    Forall (fun l => wl_wf (drop 1 (wl_words l))) (take q bs) ->
    Forall (fun l => wl_nl ∉ l) bs -> Forall (fun l => wl_nl ∉ l) bs' ->
    wl_nl ∉ t' -> wl_nl ∉ t ->
    (alt_seq ps' cs' bs' q' ++ t') `prefix_of` (alt_seq ps cs bs q ++ t) ->
    (q' <= q)%nat /\ take q' bs' = take q' bs
    /\ (pro_idx cs q' < pro_rounds ps)%nat
    /\ alt_seq ps' cs' bs' q' = alt_seq ps cs bs q'
    /\ (q' = q -> t' `prefix_of` t)
    /\ (q' < q -> t' `prefix_of` bs !!! q').
Proof.
  induction q' as [| n IH];
    intros ps ps' cs cs' bs bs' q t' t Hps Hps' Hlt' Hpos Hbelow Htlast
      Hcs Hcs' Hlb' Hlb Hwf Hnb Hnb' Hnt' Hnt Hpre.
  { rewrite alt_seq_0 app_nil_l in Hpre.
    split; [lia |]. split; [by rewrite !take_0 |].
    split; [cbn [pro_idx]; lia |]. split; [reflexivity |].
    split.
    - intros Hq. rewrite -Hq alt_seq_0 app_nil_l in Hpre. exact Hpre.
    - intros Hq. destruct q as [| p]; [lia |].
      rewrite alt_seq_cons_assoc in Hpre.
      exact (wl_prefix_nonl_of_line t' (bs !!! 0%nat) _ Hnt' Hpre). }
  (* q' = S n : the primed side has a block, so the unprimed side has one *)
  destruct q as [| p].
  { exfalso. rewrite alt_seq_0 app_nil_l alt_seq_cons_assoc in Hpre.
    exact (wl_raw_line_not_prefix_nonl (bs' !!! 0%nat) _ t Hnt Hpre). }
  rewrite !alt_seq_cons_assoc in Hpre.
  assert (Hn0' : wl_nl ∉ bs' !!! 0%nat) by (apply nonl_lta; [exact Hnb' | lia]).
  assert (Hn0 : wl_nl ∉ bs !!! 0%nat) by (apply nonl_lta; [exact Hnb | lia]).
  destruct (wl_raw_line_prefix_det _ _ _ _ Hn0' Hn0 Hpre) as [Hhd Hrest].
  rewrite (alt_cont_bs ps' cs' bs' bs 0%nat Hhd) in Hrest.
  assert (Hwf0 : wl_wf (drop 1 (wl_words (bs !!! 0%nat))))
    by (apply (wf_lta bs (S p) 0%nat); [exact Hwf | lia | lia]).
  assert (Hset' : cs' !!! 0%nat = 3%nat -> (1 < pro_rounds ps')%nat).
  { intros H3. eapply Nat.le_lt_trans; [| exact Hlt'].
    rewrite -(pro_idx_S3 cs' 0%nat H3). apply pro_idx_mono. lia. }
  assert (Hsetu : cs !!! 0%nat = 3%nat ->
            (alt_seq (pro_from (pro_idx cs 1%nat) ps) (drop 1 cs) (drop 1 bs) p
             ++ t) <> [] -> (1 < pro_rounds ps)%nat).
  { intros H3 Hne. destruct p as [| p0].
    - assert (Htne : t <> []).
      { intro Hq. apply Hne. by rewrite alt_seq_0 app_nil_l Hq. }
      pose proof (Htlast Htne) as Hb1.
      rewrite (pro_idx_S3 cs 0%nat H3) in Hb1. cbn [pro_idx] in Hb1. lia.
    - pose proof (Hbelow 1%nat ltac:(lia)) as Hb1.
      rewrite (pro_idx_S3 cs 0%nat H3) in Hb1. cbn [pro_idx] in Hb1. lia. }
  destruct (alt_cont_prefix_det ps ps' cs cs' bs _ _ Hcs Hcs' Hps Hps' Hwf0
              Hset' Hsetu Hrest) as (Hround1 & Hcont & Hrest2).
  assert (Hlt1 : (pro_idx cs 1%nat < pro_rounds ps)%nat).
  { destruct (decide (cs !!! 0%nat = 3%nat)) as [H3 | H3].
    - rewrite (pro_idx_S3 cs 0%nat H3). cbn [pro_idx]. by apply Hround1.
    - rewrite (pro_idx_Sne cs 0%nat H3). cbn [pro_idx]. lia. }
  destruct (IH (pro_from (pro_idx cs 1%nat) ps)
              (pro_from (pro_idx cs' 1%nat) ps')
              (drop 1 cs) (drop 1 cs') (drop 1 bs) (drop 1 bs') p t' t
              (pro_from_Forall _ _ ps Hps) (pro_from_Forall _ _ ps' Hps'))
    as (Hle & Htk & Hrd & Heq & Hteq & Htlt).
  { rewrite pro_rounds_from.
    pose proof (pro_idx_add cs' 1%nat n) as Hadd.
    replace (1 + n)%nat with (S n) in Hadd by lia. lia. }
  { rewrite pro_rounds_from. lia. }
  { intros i Hi. rewrite pro_rounds_from.
    pose proof (pro_idx_add cs 1%nat i) as Hadd.
    replace (1 + i)%nat with (S i) in Hadd by lia.
    pose proof (Hbelow (S i) ltac:(lia)). lia. }
  { intros Htne. rewrite pro_rounds_from.
    pose proof (pro_idx_add cs 1%nat p) as Hadd.
    replace (1 + p)%nat with (S p) in Hadd by lia.
    pose proof (Htlast Htne). lia. }
  { by apply cs_ok_drop. }
  { by apply cs_ok_drop. }
  { rewrite length_drop. lia. }
  { rewrite length_drop. lia. }
  { apply Forall_lookup. intros i x Hx.
    apply lookup_take_Some in Hx as [Hx Hi].
    rewrite lookup_drop in Hx.
    assert (Htk : take (S p) bs !! (1 + i)%nat = Some x)
      by (rewrite lookup_take_lt; [exact Hx | lia]).
    exact (Forall_lookup_1 (fun l0 => wl_wf (drop 1 (wl_words l0)))
             (take (S p) bs) (1 + i)%nat x Hwf Htk). }
  { by apply epu_Forall_drop. }
  { by apply epu_Forall_drop. }
  { exact Hnt'. }
  { exact Hnt. }
  { exact Hrest2. }
  assert (Hlbn : (S n <= length bs)%nat) by lia.
  split; [lia |].
  split; [by rewrite (epu_take_S n bs' Hlb') (epu_take_S n bs Hlbn) Hhd Htk |].
  split.
  { pose proof (pro_idx_add cs 1%nat n) as Hadd.
    replace (1 + n)%nat with (S n) in Hadd by lia.
    rewrite pro_rounds_from in Hrd. lia. }
  split.
  { rewrite (alt_seq_cons ps' cs' bs' n) (alt_seq_cons ps cs bs n) Heq.
    rewrite /alt_blk Hhd (alt_cont_bs ps' cs' bs' bs 0%nat Hhd) Hcont.
    reflexivity. }
  split.
  - intros Hqe. apply Hteq. lia.
  - intros Hqlt.
    pose proof (Htlt ltac:(lia)) as H.
    rewrite lookup_total_drop in H.
    replace (1 + n)%nat with (S n) in H by lia. exact H.
Qed.

(* ...AND THE SESSION TRANSCRIPTS THEMSELVES.  This is what lets lane
   ECHO-OUT feed [next_input_of_complete] the discipline's bound at the CLAIM's
   resolution: the two are the same BYTES, and the discipline's input is a
   PREFIX of the claim's -- which is what the old index comparison
   ([i <= j]) becomes once the stage is an input. *)
Lemma sess_prefix_det (ps ps' cs cs' : list nat) (I' I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  pro_ok ps' cs' (nlines I') ->
  Forall (fun x => (x < 4)%nat) cs ->
  Forall (fun x => (x < 4)%nat) cs' ->
  pro_pin ps cs I -> disc_input I -> disc_input I' ->
  sess ps' cs' I' `prefix_of` sess ps cs I ->
  I' `prefix_of` I /\ pro_ok ps cs (nlines I')
  /\ sess ps' cs' I' = sess ps cs I'.
Proof.
  intros Hps [Hps' Hlt'] Hcs Hcs' Hpin Hd Hd' Hpre.
  pose proof (cs_ok_of_Forall _ Hcs) as Hok.
  pose proof (cs_ok_of_Forall _ Hcs') as Hok'.
  assert (Hdone' : pro_done ps') by (apply pro_done_rounds; lia).
  (* the PROLOGUES: below one wire, and the primed one is settled, so they
     are the same prologue and the unprimed one is settled too *)
  assert (Hpre0 : pro_of ps' `prefix_of` pro_of ps).
  { destruct (decide (I = [])) as [HI0 | HI].
    - rewrite HI0 sess_nil in Hpre. etrans; [| exact Hpre].
      rewrite /sess. by apply prefix_app_r.
    - assert (HdA : pro_done ps).
      { apply pro_done_rounds.
        pose proof (Hpin 0%nat (nstarted_pos I HI)) as H0.
        cbn [pro_idx] in H0. lia. }
      assert (H1 : pro_of ps' `prefix_of` sess ps cs I).
      { etrans; [| exact Hpre]. rewrite /sess. by apply prefix_app_r. }
      assert (H2 : pro_of ps `prefix_of` sess ps cs I)
        by (rewrite /sess; by apply prefix_app_r).
      destruct (prefix_weak_total _ _ _ H1 H2) as [H | H]; [exact H |].
      destruct (pro_of_prefix_free ps' ps Hps' Hps HdA H) as [_ Heq].
      by rewrite Heq. }
  destruct (pro_of_prefix_free ps ps' Hps Hps' Hdone' Hpre0) as [Hdps Heq0].
  assert (Hpos : (0 < pro_rounds ps)%nat) by (by apply pro_done_rounds).
  rewrite /sess Heq0 in Hpre. apply prefix_app_inv in Hpre.
  assert (Hbelow : forall i, (i < nlines I)%nat ->
            (pro_idx cs i < pro_rounds ps)%nat).
  { intros i Hi. apply Hpin. pose proof (nlines_le_nstarted I). lia. }
  assert (Htlast : rest_of I <> [] ->
            (pro_idx cs (nlines I) < pro_rounds ps)%nat).
  { intros Hne. apply Hpin. rewrite /nstarted.
    case_decide as Hz; [by destruct (Hne Hz) | lia]. }
  assert (Hlb' : (nlines I' <= length (bodies_of I'))%nat)
    by (rewrite /nlines; lia).
  assert (Hlb : (nlines I <= length (bodies_of I))%nat)
    by (rewrite /nlines; lia).
  assert (Hwfb : Forall (fun l => wl_wf (drop 1 (wl_words l)))
                   (take (nlines I) (bodies_of I))).
  { rewrite take_ge; [| rewrite /nlines; lia].
    destruct Hd as (Hb & _ & _).
    eapply Forall_impl; [exact Hb |].
    intros l [_ Hok2]. rewrite /wl_wf.
    apply epu_Forall_drop. exact (line_ok_wf _ Hok2). }
  destruct (alt_seq_prefix_det (nlines I') ps ps' cs cs' (bodies_of I)
              (bodies_of I') (nlines I) (rest_of I') (rest_of I)
              Hps Hps' Hlt' Hpos Hbelow Htlast Hok Hok' Hlb' Hlb Hwfb
              (wl_cut_bodies_nonl I) (wl_cut_bodies_nonl I')
              (wl_cut_rest_nonl I') (wl_cut_rest_nonl I) Hpre)
    as (Hqle & Htk & Hround & Hseq & Hteq & Htlt).
  assert (HI' : I' `prefix_of` I).
  { apply wl_cut_prefix_of.
    - assert (Hb' : bodies_of I' = take (nlines I') (bodies_of I))
        by (rewrite -Htk take_ge; [reflexivity | rewrite /nlines; lia]).
      rewrite Hb'. apply prefix_take.
    - exact Hteq.
    - exact Htlt. }
  split; [exact HI' |]. split; [split; [exact Hps | exact Hround] |].
  rewrite /sess Heq0. do 2 f_equal. rewrite Hseq.
  apply alt_seq_bs_ext. intros j Hj. symmetry.
  exact (lta_of_take_eq (bodies_of I) (bodies_of I') (nlines I') j Htk Hj).
Qed.

(* the open cycle's FULL discipline, not only D3 -- [disc_seg_open_seg]'s
   twin, and the one lane ECHO-OUT's echo step spends *)
Lemma disc_seg'_open_seg (h : list mobs) :
  trace_shape h true -> disc h -> disc_seg' (open_seg h).
Proof.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply list_elem_of_lookup in Hin as [i Hi].
  exact (Forall_lookup_1 _ _ _ _ Hd Hi).
Qed.

Lemma epu_removelast_snoc {A} (l : list A) (a : A) : removelast (l ++ [a]) = l.
Proof.
  induction l as [| b l IH]; [reflexivity |].
  change ((b :: l) ++ [a]) with (b :: (l ++ [a])).
  assert (Hne : l ++ [a] <> [])
    by (intro Hq; by apply app_eq_nil in Hq as [_ ?]).
  destruct (l ++ [a]) as [| z zs] eqn:Hz; [by destruct (Hne eq_refl) |].
  change (removelast (b :: z :: zs)) with (b :: removelast (z :: zs)).
  by rewrite IH.
Qed.

(* THE DISCIPLINE'S LOWER BOUND AT THE OPEN CYCLE'S LAST INPUT: D1 read
   off [disc_seg'] at the wire the last byte was typed on, which is what
   F2's [Hlow] is.  The bound is at the COMPLETE LINES of the input before
   that byte ([LineWords.done_of]); [pro_ok] is at [nlines], which the
   truncation leaves alone ([LineWords.nlines_done]).  The resolution is
   the DISCIPLINE's; [sess_prefix_det] is what moves the bound to the
   claim's. *)
Lemma disc_seg'_pt_last (seg : list mobs) (c : bv 8) :
  disc_seg' seg -> obs_ends_in Uart0 seg c ->
  exists ps' cs' : list nat,
    pro_ok ps' cs' (nlines (removelast (ins seg)))
    /\ Forall (fun x => (x < 4)%nat) cs'
    /\ sess ps' cs' (done_of (removelast (ins seg)))
         `prefix_of` obs_wire Uart0 seg.
Proof.
  intros [Hd (ps & cs & Hlen & Hf & Hall)] [seg0 ->].
  exists ps, cs.
  assert (Hip : seg0 ∈ in_pres (seg0 ++ [ObsUartIn Uart0 c])).
  { rewrite in_pres_in. apply elem_of_app. right. apply list_elem_of_here. }
  destruct (Hall _ Hip) as [Hok Hpt]. rewrite /disc_pt in Hpt.
  rewrite ins_app ins_in epu_removelast_snoc.
  split; [exact Hok |]. split; [exact Hf |].
  etrans; [exact Hpt |]. rewrite obs_wire_app. by eexists.
Qed.

(* [sess] is never empty once round 0 has settled: it begins with the
   prologue, and a settled prologue has at least its ending letter's bytes
   (an OPEN round with nothing filed predicts nothing, so the resolution
   has to be settled) *)
Lemma u_prologue_pos : 0 < length u_prologue.
Proof. vm_compute. lia. Qed.

Lemma sess_nonnil (ps cs : list nat) (I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> pro_done ps ->
  sess ps cs I <> [].
Proof.
  intros HF Hd H. apply (f_equal length) in H.
  rewrite sess_length in H.
  change (length (@nil (bv 8))) with 0%nat in H.
  assert (Hne : ps <> []) by (intros ->; by apply Exists_nil in Hd).
  pose proof (pro_of_pos ps HF Hne). lia.
Qed.

(* ---- THE RECEIVE FLUSH LOSES NOTHING UNDER THE DISCIPLINE ------------- *)

(* uartinit's FCR write clears the receive FIFO, so the kernel's log can
   only be complete up to the bytes the environment pushed before the
   console existed ([ConsLog.flush_lost]).  The kernel says WHEN those bytes
   were taken -- inside a prefix of the era's segment that carries NO
   console output -- and the discipline says there are none: D1 asks the
   prologue to be on the wire before the era's FIRST input, and the prologue
   is not empty. *)

(* [in_pres]'s index law: the [i]-th pre-history holds exactly [i] inputs.
   It is the reading [in_pres_length] gives at every prefix at once, and
   what the discipline is instantiated at below (at [i = 0], the empty
   input). *)
Lemma in_pres_lookup_ins (seg : list mobs) (i : nat) (p : list mobs) :
  in_pres seg !! i = Some p -> length (ins p) = i.
Proof.
  revert i p. induction seg as [| e seg IH] using rev_ind; intros i p Hp.
  - cbn [in_pres] in Hp. rewrite lookup_nil in Hp. discriminate Hp.
  - destruct e as [ii b | ii b | |]; [destruct ii | | |].
    + rewrite in_pres_in in Hp.
      destruct (decide (i < length (in_pres seg))%nat) as [Hlt | Hge].
      { rewrite lookup_app_l in Hp; [| exact Hlt]. exact (IH i p Hp). }
      rewrite lookup_app_r in Hp; [| lia].
      assert (Hi : i = length (in_pres seg)).
      { apply lookup_lt_Some in Hp. cbn [length] in Hp. lia. }
      rewrite Hi Nat.sub_diag in Hp. cbn in Hp. injection Hp as <-.
      by rewrite Hi in_pres_length.
    + rewrite (in_pres_snoc_other seg (ObsUartIn Uart1 b) I) in Hp.
      exact (IH i p Hp).
    + rewrite (in_pres_snoc_other seg (ObsUartOut ii b) I) in Hp.
      exact (IH i p Hp).
    + rewrite (in_pres_snoc_other seg ObsPowerOn I) in Hp. exact (IH i p Hp).
    + rewrite (in_pres_snoc_other seg ObsPowerOff I) in Hp. exact (IH i p Hp).
Qed.

(* ...and the list of pre-histories grows with the segment, which is how a
   pre-history of a PREFIX is one the segment's own discipline speaks about *)
Lemma in_pres_mono (s1 s2 : list mobs) :
  s1 `prefix_of` s2 -> in_pres s1 `prefix_of` in_pres s2.
Proof.
  intros [k ->]. induction k as [| e k IH] using rev_ind.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. etrans; [exact IH |].
    destruct e as [ii b | ii b | |]; [destruct ii | | |].
    + rewrite in_pres_in. by eexists.
    + rewrite (in_pres_snoc_other _ (ObsUartIn Uart1 b) I). reflexivity.
    + rewrite (in_pres_snoc_other _ (ObsUartOut ii b) I). reflexivity.
    + rewrite (in_pres_snoc_other _ ObsPowerOn I). reflexivity.
    + rewrite (in_pres_snoc_other _ ObsPowerOff I). reflexivity.
Qed.

(* A DISCIPLINED SEGMENT HAS NO INPUT BEFORE ITS FIRST OUTPUT, so the window
   the flush could have eaten is empty.  [sf] is that window: a prefix of
   the era's segment with nothing on the wire.  If it held an input, the
   pre-history [p0] of its FIRST one would be a pre-history of the whole
   segment at the EMPTY input, and D1 there demands the prologue --
   nonempty once its round has settled ([sess_nonnil]) -- on a wire that is
   a prefix of [sf]'s, which is empty. *)
Lemma flush_lost_disc (seg sf : list mobs) (f : nat) :
  disc_seg' seg -> sf `prefix_of` seg ->
  obs_wire Uart0 sf = [] -> length (obs_ins Uart0 sf) = f -> f = 0%nat.
Proof.
  intros Hd Hpre Hw Hlen.
  destruct (decide (f = 0%nat)) as [Hz | Hne]; [exact Hz | exfalso].
  (* the wire the user had seen when [sf]'s first byte was typed *)
  assert (Hlp : (0 < length (in_pres sf))%nat)
    by (rewrite in_pres_length /ins; lia).
  destruct (lookup_lt_is_Some_2 (in_pres sf) 0%nat Hlp) as [p0 Hp0].
  assert (Hins0 : ins p0 = [])
    by (apply nil_length_inv; exact (in_pres_lookup_ins sf 0%nat p0 Hp0)).
  (* it is one of the SEGMENT's pre-histories, and its wire is empty *)
  assert (Hp0seg : p0 ∈ in_pres seg).
  { apply list_elem_of_lookup_2 with 0%nat.
    destruct (in_pres_mono sf seg Hpre) as [z Hz].
    rewrite Hz lookup_app_l; [exact Hp0 | lia]. }
  assert (Hw0 : obs_wire Uart0 p0 = []).
  { destruct (in_pres_prefix sf 0%nat p0 Hp0) as [z Hz].
    rewrite Hz obs_wire_app in Hw. by apply app_eq_nil in Hw as [Hw _]. }
  (* D1 at the empty input asks for the prologue, and there is no room *)
  destruct Hd as [_ (ps & cs & _ & _ & Hall)].
  destruct (Hall p0 Hp0seg) as [Hok Hpt].
  destruct Hok as [HF Hlt].
  apply (sess_nonnil ps cs [] HF (proj2 (pro_done_rounds ps) ltac:(lia))).
  apply prefix_nil_inv.
  rewrite /disc_pt Hins0 done_of_nil Hw0 in Hpt. exact Hpt.
Qed.

(* ...at the shape [ConsLog.cons_ev_ok] hands the claim at [EvOpen] *)
Lemma flush_lost_zero (h : list mobs) (f : nat) :
  trace_shape h true -> disc h -> ConsLog.flush_lost h f -> f = 0%nat.
Proof.
  intros Hsh Hdisc [Hz | (sf & Hpre & Hw & Hlen)]; [exact Hz |].
  exact (flush_lost_disc (open_seg h) sf f
           (disc_seg'_open_seg h Hsh Hdisc) Hpre Hw Hlen).
Qed.

(* ====================================================================== *)
(*  10.  THE SAME-CYCLE BRIDGE (lane ECHO-OUT, section 7)                  *)
(*                                                                        *)
(*  The claims record their same-cycle facts at their OWN witness history  *)
(*  [ho]; the ledger's drain reads them at the run's history [h], and the  *)
(*  kernel supplies [ho `prefix_of` h] ([App.Htx]) and the era stamp at    *)
(*  both ends.  What is missing is the step from “a prefix, at the same    *)
(*  boot count” to "a prefix of the OPEN SEGMENT" -- and that is exactly   *)
(*  where the boot count earns its keep: a suffix with no PowerOn in it    *)
(*  cannot contain a PowerOff either, because the machine is ON at the     *)
(*  end and only a PowerOn turns it back on.                              *)
(* ====================================================================== *)

Lemma epu_foldl_obs_step_none (h : list mobs) :
  foldl obs_step None h = None.
Proof. induction h as [| e h IH]; [done |]. by cbn. Qed.

Lemma epu_no_power_of_boots (h : list mobs) (st : bool) :
  obs_boots h = 0%nat ->
  foldl obs_step (Some st) h = Some true ->
  st = true /\ Forall (fun e => is_io e = true) h.
Proof.
  revert st. induction h as [| e h IH]; intros st Hb Hf.
  - cbn in Hf. injection Hf as ->. split; [reflexivity | constructor].
  - destruct e as [i b | i b | |]; cbn in Hb.
    + cbn in Hf. destruct st.
      * destruct (IH true Hb Hf) as [_ HF].
        split; [reflexivity | by constructor].
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
    + cbn in Hf. destruct st.
      * destruct (IH true Hb Hf) as [_ HF].
        split; [reflexivity | by constructor].
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
    + (* ObsPowerOn *) lia.
    + (* ObsPowerOff *)
      cbn in Hf. destruct st.
      * destruct (IH false Hb Hf) as [Habs _]. discriminate.
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
Qed.

Lemma open_seg_prefix_boots (h1 h2 : list mobs) :
  h1 `prefix_of` h2 -> obs_boots h1 = obs_boots h2 ->
  trace_shape h2 true -> open_seg h1 `prefix_of` open_seg h2.
Proof.
  intros [k ->] Hb Hsh.
  assert (Hk : obs_boots k = 0%nat)
    by (rewrite obs_boots_app in Hb; lia).
  rewrite /trace_shape foldl_app in Hsh.
  destruct (foldl obs_step (Some false) h1) as [st |] eqn:Hst; last first.
  { rewrite epu_foldl_obs_step_none in Hsh. discriminate. }
  destruct (epu_no_power_of_boots k st Hk Hsh) as [_ HF].
  rewrite (open_seg_io h1 k HF). by eexists.
Qed.

Lemma ins_prefix_of (s1 s2 : list mobs) :
  s1 `prefix_of` s2 -> ins s1 `prefix_of` ins s2.
Proof. intros [z ->]. rewrite ins_app. by eexists. Qed.
