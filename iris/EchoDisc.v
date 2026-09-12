(* EchoDisc.v -- THE ECHO APPLICATION'S CONSOLE DISCIPLINE AND OUTPUT CLAIM,
   as PURE COMBINATORICS over the observation trace.  No Iris, no ghosts: a
   [list mobs] goes in and a [Prop] comes out, so the statements here can be
   read -- and refuted -- without opening the logic.

   Design of record: claude-notes/projects/app-echo.md, "E5 -- THE OUTPUT
   SIDE" (O1-O3 AS RULED BY THE OWNER, D0-D3; O5's allocation-failure
   alternatives) and "E3 -- THE INPUT LINE" (R4, the per-character ruling);
   the pre-mortem review review-echo-plan-2026-09-12.md, findings 2, 7, 8
   and 12.

   WHY THIS FILE EXISTS.  [AppEcho.disc] used to be [star_prefix echo_line]
   of the cycle's INPUT BYTES ALONE -- a predicate that says nothing about
   WHEN a byte was typed.  Review finding 7 is that the theorem is FALSE at
   that discipline: the console ring holds 128 unconsumed bytes and
   [consoleintr] DROPS the next one silently, so an adversary who types a
   screenful before sh's first read breaks the correspondence between the
   stored sequence and the input sequence, and nothing downstream can
   repair it.  The owner's ruling (app-echo.md, O3 (d)) is a RATE BOUND
   stated on the raw wire:

     D0  no input byte until all seven "hart i starting\n" lines have
         appeared on the wire as SUBSEQUENCES.  The three hart-0 banners
         precede [userinit] and so precede every user byte, and the seven
         secondaries print at times the scheduler picks; after the last of
         them no kernel [printk] byte is ever accepted again in this
         scenario, so the wire's suffix from that point on is PURE U -- the
         processes' own output and the console's echo.  That is what makes
         D1 and D2 unambiguous.
     D1  a line's first byte only after a "$ " prompt on the pure suffix.
     D2  every later byte only after the previous byte's echo.
     D3  the input bytes are a prefix of [echo_line]^* -- the LANDED
         predicate, kept verbatim as [disc_seg].

   D0'S UNAMBIGUITY is section 5 and it is CHEAP: every "hart i starting\n"
   carries a DECIMAL DIGIT, and the whole U alphabet -- init's banner, sh's
   prompt, the echoes, echo's output, and every one of O5's failure
   transcripts -- contains no digit at all.  So no prefix of the expected
   session can be mistaken for a hart's boot message, whatever the
   scheduler does.

   D1 AND D2 ARE ONE CONDITION, POSITIONAL.  Rather than "byte i-1's echo
   has appeared" beside "a prompt has appeared", section 6 states, at every
   input position i, that the WHOLE expected transcript for the first i
   input bytes is already a prefix of the wire's pure suffix ([disc_pt]).
   The transcript for i bytes ENDS in exactly the byte D2 asks for when i
   is mid-line, and in exactly the "$ " D1 asks for when i is at a line
   boundary, so the one condition implies both; and it is the SIMULATION
   INVARIANT the output proof wants, because [good_out] bounds the same
   suffix from the other side.  At an input point the two bounds meet and
   the U-projection of the wire is pinned exactly.

   WHAT IS NOT HERE.  [Hphi] -- the theorem's obligation at [echo_phi] --
   is NOT proved by this file, nor by the lane that wrote it; see the note
   at [AppEcho.echo_phi].  This file is the STATEMENT. *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [obs_wire], [cycles_of], [trace_shape] *)
Require Import RiscvPtsto.       (* [string_bytes] *)
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
(*  1.  THE BOOT MESSAGES (R1)                                            *)
(*                                                                        *)
(*  kernel/main.c: hart 0 prints "\n", "xv6 kernel is booting\n", "\n"     *)
(*  BEFORE userinit() and before it sets [started]; every other hart spins *)
(*  on [started] and then prints "hart %d starting\n" of its own cpuid.    *)
(*  [RiscvLang.NCPU] is 8, so there are SEVEN such lines and TEN messages  *)
(*  in all (the brief's "eight" counts hart 0's three as one).  printk     *)
(*  holds pr.lock for a whole message, so the ten do not interleave WITH   *)
(*  EACH OTHER -- but their bytes do interleave with everything else,      *)
(*  which is what section 7's shuffle is about.  "%d" of 1..7 is ONE       *)
(*  decimal digit (kernel/printk.c, printint).                             *)
(* ====================================================================== *)

Definition msg_nl : list (bv 8) := nlb.
Definition msg_booting : list (bv 8) := sb "xv6 kernel is booting"%string ++ nlb.

Definition hart_line (n : Z) : list (bv 8) :=
  sb "hart "%string ++ [Z_to_bv 8 (48 + n)%Z] ++ sb " starting"%string ++ nlb.

Definition hart_lines : list (list (bv 8)) := hart_line <$> [1;2;3;4;5;6;7]%Z.

Definition boot_msgs : list (list (bv 8)) :=
  [msg_nl; msg_booting; msg_nl] ++ hart_lines.

Lemma hart_lines_length : length hart_lines = 7.
Proof. reflexivity. Qed.
Lemma boot_msgs_length : length boot_msgs = 10.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(*  2.  THE PURE-SUFFIX POINT (R2)                                         *)
(*                                                                        *)
(*  [k_done w]: every hart line has appeared in [w] as a SUBSEQUENCE --    *)
(*  stdpp's [sublist], the bytes in order but not necessarily adjacent,    *)
(*  which is what a byte-level interleave leaves of a message.             *)
(*  [k_point w] is the LEAST prefix length at which that became true.      *)
(* ====================================================================== *)

(* stdpp has no decision procedure for [sublist]; the greedy leftmost match
   is one, and the discipline has to stay decidable ([AppEcho.echo_phase]
   decides it). *)
Fixpoint subseqb `{EqDecision A} (l1 l2 : list A) : bool :=
  match l2 with
  | [] => match l1 with [] => true | _ => false end
  | y :: l2' =>
      match l1 with
      | [] => true
      | x :: l1' => if decide (x = y) then subseqb l1' l2' else subseqb l1 l2'
      end
  end.

Lemma subseqb_spec `{EqDecision A} (l1 l2 : list A) :
  subseqb l1 l2 = true <-> l1 `sublist_of` l2.
Proof.
  revert l1. induction l2 as [|y l2 IH]; intros l1.
  - destruct l1 as [|a l1]; cbn; split.
    + intros _. constructor.
    + intros _. reflexivity.
    + intros Hf. discriminate Hf.
    + intros Hs. apply sublist_nil_r in Hs. discriminate Hs.
  - destruct l1 as [|x l1]; cbn.
    { split; [intros _; apply sublist_nil_l | intros _; reflexivity]. }
    destruct (decide (x = y)) as [->|Hne].
    + rewrite IH. split.
      * intros Hs. by apply sublist_skip.
      * intros Hs. apply sublist_cons_r in Hs as [Hs|(l' & Heq & Hs)].
        { trans (y :: l1); [by apply sublist_cons | exact Hs]. }
        by simplify_eq.
    + rewrite IH. split.
      * intros Hs. by apply sublist_cons.
      * intros Hs. apply sublist_cons_r in Hs as [Hs|(l' & Heq & Hs)];
          [exact Hs | by simplify_eq].
Qed.

Global Instance sublist_byte_dec (l1 l2 : list (bv 8)) :
  Decision (l1 `sublist_of` l2).
Proof.
  destruct (subseqb l1 l2) eqn:E; [left|right].
  - by apply subseqb_spec.
  - intros Hs. apply subseqb_spec in Hs. by rewrite E in Hs.
Qed.

Definition k_done (w : list (bv 8)) : Prop :=
  Forall (fun l => l `sublist_of` w) hart_lines.

Global Instance k_done_dec w : Decision (k_done w).
Proof. unfold k_done. apply _. Qed.

(* the least index at which a boolean test first holds, scanning upwards *)
Fixpoint first_from (f : nat -> bool) (i n : nat) : option nat :=
  match n with
  | O => None
  | S n' => if f i then Some i else first_from f (S i) n'
  end.

Lemma first_from_Some (f : nat -> bool) (i n k : nat) :
  first_from f i n = Some k ->
  i <= k < i + n /\ f k = true /\ (forall j, i <= j < k -> f j = false).
Proof.
  revert i. induction n as [|n IH]; intros i Hf; [discriminate|].
  cbn in Hf. destruct (f i) eqn:Hi.
  - injection Hf as <-. split; [lia|]. split; [exact Hi|]. intros j Hj. lia.
  - destruct (IH _ Hf) as (Hr & Hk & Hlt). split; [lia|]. split; [exact Hk|].
    intros j Hj. destruct (decide (j = i)) as [->|Hne]; [exact Hi|].
    apply Hlt. lia.
Qed.

Lemma first_from_None (f : nat -> bool) (i n j : nat) :
  first_from f i n = None -> i <= j < i + n -> f j = false.
Proof.
  revert i. induction n as [|n IH]; intros i Hf Hj; [lia|].
  cbn in Hf. destruct (f i) eqn:Hi; [discriminate|].
  destruct (decide (j = i)) as [->|Hne]; [exact Hi|].
  apply (IH (S i) Hf). lia.
Qed.

Lemma first_from_true (f : nat -> bool) (i n j : nat) :
  i <= j < i + n -> f j = true -> exists k, first_from f i n = Some k.
Proof.
  intros Hj Hfj. destruct (first_from f i n) as [k|] eqn:E; [by eexists|].
  by rewrite (first_from_None _ _ _ _ E Hj) in Hfj.
Qed.

Definition k_point (w : list (bv 8)) : option nat :=
  first_from (fun k => bool_decide (k_done (take k w))) 0 (S (length w)).

(* the point itself, with the harmless total default: past the end of the
   wire, which is where "the harts have not all printed" leaves it *)
Definition k_pt (w : list (bv 8)) : nat := from_option id (length w) (k_point w).

Lemma k_point_done (w : list (bv 8)) (k : nat) :
  k_point w = Some k -> k_done (take k w) /\ k <= length w.
Proof.
  intros Hk. apply first_from_Some in Hk as (Hr & Ht & _).
  split; [exact (bool_decide_eq_true_1 _ Ht) | lia].
Qed.

Lemma k_point_least (w : list (bv 8)) (k j : nat) :
  k_point w = Some k -> j <= length w -> k_done (take j w) -> k <= j.
Proof.
  intros Hk Hj Hd. apply first_from_Some in Hk as (_ & _ & Hlt).
  destruct (decide (k <= j)) as [Hle|Hgt]; [exact Hle|]. exfalso.
  assert (Hf : bool_decide (k_done (take j w)) = false) by (apply Hlt; lia).
  by rewrite (bool_decide_eq_true_2 _ Hd) in Hf.
Qed.

Lemma k_done_k_point (w : list (bv 8)) :
  k_done w -> exists k, k_point w = Some k.
Proof.
  intros Hd. apply (first_from_true _ 0 (S (length w)) (length w)); [lia|].
  apply bool_decide_eq_true_2. rewrite take_ge; [exact Hd|done].
Qed.

Lemma k_point_None (w : list (bv 8)) :
  (forall k, k <= length w -> ~ k_done (take k w)) -> k_point w = None.
Proof.
  intros Hn. destruct (k_point w) as [k|] eqn:E; [|done].
  apply k_point_done in E as [Hd Hk]. by destruct (Hn k Hk).
Qed.

(* ====================================================================== *)
(*  3.  THE INPUT LINE AND D3 (the landed predicate, verbatim)             *)
(* ====================================================================== *)

(* the console line the discipline admits: "echo hello world\n" -- the
   bytes the user types, and ALSO their echoes, because [consoleintr]
   echoes a stored byte unchanged and rewrites only '\r' (to '\n').  This
   line ends in '\n' (byte 10), not '\r', so echo is the IDENTITY on it. *)
Definition echo_line : list (bv 8) :=
  Z_to_bv 8 <$> [101; 99; 104; 111; 32; 104; 101; 108; 108; 111; 32;
                 119; 111; 114; 108; 100; 10]%Z.

Lemma echo_line_length : length echo_line = 17.
Proof. reflexivity. Qed.
Lemma echo_line_pos : 0 < length echo_line.
Proof. rewrite echo_line_length. lia. Qed.

(* the same line, read off the string it is: a transcription check *)
Lemma echo_line_string : echo_line = sb "echo hello world"%string ++ nlb.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* the INPUT bytes of an observation list, in order *)
Definition ins (h : list mobs) : list (bv 8) :=
  omap (fun e => match e with ObsUartIn b => Some b | _ => None end) h.

Lemma ins_app (h k : list mobs) : ins (h ++ k) = ins h ++ ins k.
Proof. by rewrite /ins omap_app. Qed.

Lemma ins_in (b : bv 8) : ins [ObsUartIn b] = [b].
Proof. reflexivity. Qed.
Lemma ins_out (b : bv 8) : ins [ObsUartOut b] = [].
Proof. reflexivity. Qed.

(* [l] IS A PREFIX OF [pat]^*, spelled so that it is decidable by one
   list equality and prefix-closed by one [take]: the first [length l]
   letters of [pat] repeated [length l] times are the first [length l]
   letters of [pat]^w whenever [pat] is nonempty. *)
Definition star_prefix (pat l : list (bv 8)) : Prop :=
  l = take (length l) (concat (replicate (length l) pat)).

Global Instance star_prefix_dec pat l : Decision (star_prefix pat l).
Proof. rewrite /star_prefix. apply _. Qed.

Lemma star_prefix_nil pat : star_prefix pat [].
Proof. reflexivity. Qed.

Lemma concat_replicate_S {A} (n : nat) (pat : list A) :
  concat (replicate (S n) pat) = concat (replicate n pat) ++ pat.
Proof. by rewrite replicate_S_end concat_app /= app_nil_r. Qed.

Lemma concat_replicate_length {A} (n : nat) (pat : list A) :
  length (concat (replicate n pat)) = n * length pat.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite concat_replicate_S length_app IH. lia.
Qed.

(* the one law the rx step needs: breaking the discipline is forever. *)
Lemma star_prefix_snoc pat l b :
  0 < length pat ->
  star_prefix pat (l ++ [b]) -> star_prefix pat l.
Proof.
  rewrite /star_prefix. intros Hpat Hsnoc.
  apply (f_equal (take (length l))) in Hsnoc.
  rewrite take_app_length take_take in Hsnoc.
  rewrite length_app /= in Hsnoc.
  rewrite Nat.min_l in Hsnoc; [|lia].
  rewrite Nat.add_1_r concat_replicate_S in Hsnoc.
  rewrite take_app_le in Hsnoc; [exact Hsnoc|].
  rewrite concat_replicate_length. nia.
Qed.

(* D3: one power cycle's input keeps the CONTENT discipline.  This is the
   whole of the LANDED [AppEcho.disc_seg]; [UConsLine]'s line statements
   are written at it and are unchanged (section 6's projection). *)
Definition disc_seg (seg : list mobs) : Prop := star_prefix echo_line (ins seg).

Global Instance disc_seg_dec seg : Decision (disc_seg seg).
Proof. rewrite /disc_seg. apply _. Qed.

Lemma disc_seg_nil : disc_seg [].
Proof. exact (star_prefix_nil _). Qed.

Lemma disc_seg_out (seg : list mobs) (b : bv 8) :
  disc_seg (seg ++ [ObsUartOut b]) <-> disc_seg seg.
Proof. rewrite /disc_seg ins_app ins_out app_nil_r. done. Qed.

(* THE LANDED WHOLE-HISTORY PREDICATE, kept under its own name: everything
   already proved against it still means what it meant, and section 6's
   [disc_proj] is the one step from the new discipline to it. *)
Definition disc_old (h : list mobs) : Prop := Forall disc_seg (cycles_of h).

Global Instance disc_old_dec h : Decision (disc_old h).
Proof. rewrite /disc_old. apply _. Qed.

(* ====================================================================== *)
(*  4.  THE EXPECTED SESSION (R3, with O5's alternatives)                  *)
(* ====================================================================== *)

(* user/init.c:26 and user/sh.c:137 -- init's banner, then sh's prompt. *)
Definition u_prologue : list (bv 8) :=
  sb "init: starting sh"%string ++ nlb ++ sb "$ "%string.

(* O5, RULED BY THE OWNER (2026-09-12): allocation failure PRINTS, and what
   it prints is valid output.  After a complete line's '\n' echo the
   continuation is ONE OF
     0  "hello world\n$ "                 the good one: echo ran
     1  "exec echo failed\n$ "            sh's child could not exec
                                          (user/sh.c:80); it exits 0
     2  "$ "                              the child died before printing
     3  "fork\ninit: starting sh\n$ "     sh's fork1 panicked
                                          (user/sh.c:194; panic prints
                                          "%s\n" to fd 2 and exits 1), so
                                          init reaps and restarts sh
   Every alternative ENDS in "$ ", so D1's "a prompt has appeared" is
   well-defined after any of them; and their FIRST bytes are 'h', 'e', '$',
   'f' -- pairwise distinct, which is what makes the choice readable off
   the wire.  A later ruling changes this ONE list. *)
Definition line_alts : list (list (bv 8)) :=
  [ sb "hello world"%string ++ nlb ++ sb "$ "%string;
    sb "exec echo failed"%string ++ nlb ++ sb "$ "%string;
    sb "$ "%string;
    sb "fork"%string ++ nlb ++ sb "init: starting sh"%string ++ nlb
      ++ sb "$ "%string ].

Lemma line_alts_length : length line_alts = 4.
Proof. reflexivity. Qed.

(* ONE COMPLETED LINE'S OUTPUT: the echo of its seventeen bytes, then the
   continuation this run took.  [cs] records the continuation per line; out
   of range it reads as alternative 0, which keeps [alt_seq] total and its
   step law unconditional -- the choice is pinned by the wire wherever the
   discipline actually looks at it. *)
Definition alt_blk (cs : list nat) (i : nat) : list (bv 8) :=
  echo_line ++ line_alts !!! (cs !!! i).

Definition alt_seq (cs : list nat) (q : nat) : list (bv 8) :=
  concat (alt_blk cs <$> List.seq 0 q).

Lemma alt_seq_0 cs : alt_seq cs 0 = [].
Proof. reflexivity. Qed.

Lemma alt_seq_S cs q : alt_seq cs (S q) = alt_seq cs q ++ alt_blk cs q.
Proof.
  rewrite /alt_seq List.seq_S fmap_app concat_app Nat.add_0_l /=.
  by rewrite app_nil_r.
Qed.

(* THE EXPECTED SESSION TRANSCRIPT for [n] input bytes: init's banner and
   the first prompt, then one block per COMPLETED line, then the echo of
   the bytes of the line in progress.  It depends on the input only through
   its LENGTH -- which is what D3 buys: under [disc_seg] the input IS
   determined by its length. *)
Definition sess_n (cs : list nat) (n : nat) : list (bv 8) :=
  u_prologue ++ alt_seq cs (n `div` length echo_line)
             ++ take (n `mod` length echo_line) echo_line.

Definition sess (cs : list nat) (l : list (bv 8)) : list (bv 8) :=
  sess_n cs (length l).

(* R3's relation: [out] is what the session may have emitted for input [l],
   under SOME resolution of the per-line alternatives. *)
Definition expected_rel (l out : list (bv 8)) : Prop :=
  exists cs : list nat,
    Forall (fun c => c < length line_alts) cs /\ out `prefix_of` sess cs l.

(* ---- the arithmetic of one more input byte ---- *)

Lemma div_mod_succ (n m : nat) :
  0 < m ->
  (S n `mod` m = 0 /\ S n `div` m = S (n `div` m) /\ n `mod` m = m - 1)
  \/ (S n `mod` m = S (n `mod` m) /\ S n `div` m = n `div` m).
Proof.
  intros Hm.
  pose proof (Nat.div_mod_eq n m) as Hdm.
  pose proof (Nat.mod_upper_bound n m ltac:(lia)) as Hub.
  destruct (decide (S (n `mod` m) = m)) as [Heq|Hne].
  - left.
    assert (HS : S n = (n `div` m + 1) * m) by nia.
    rewrite HS Nat.Div0.mod_mul Nat.div_mul; [|lia].
    split; [done|]. split; [lia|]. lia.
  - right.
    assert (HS : S n = S (n `mod` m) + n `div` m * m) by nia.
    rewrite HS Nat.Div0.mod_add Nat.mod_small; [|lia].
    split; [done|].
    rewrite Nat.div_add; [|lia]. rewrite Nat.div_small; [lia|lia].
Qed.

Lemma prefix_take_le {A} (l : list A) (n m : nat) :
  n <= m -> take n l `prefix_of` take m l.
Proof.
  intros Hnm.
  assert (H : take n l = take n (take m l)).
  { rewrite take_take Nat.min_l; [done|lia]. }
  rewrite H. apply prefix_take.
Qed.

Lemma sess_n_step cs n : sess_n cs n `prefix_of` sess_n cs (S n).
Proof.
  rewrite /sess_n.
  destruct (div_mod_succ n (length echo_line) echo_line_pos)
    as [(Hm & Hd & Hr)|(Hm & Hd)]; rewrite Hm Hd.
  - rewrite alt_seq_S take_0 app_nil_r.
    apply prefix_app, prefix_app.
    rewrite /alt_blk. apply prefix_app_r, prefix_take.
  - apply prefix_app, prefix_app, prefix_take_le. lia.
Qed.

Lemma sess_n_mono cs n m : n <= m -> sess_n cs n `prefix_of` sess_n cs m.
Proof.
  intros Hnm. replace m with (n + (m - n)) by lia.
  generalize (m - n) as d. intros d. clear Hnm m.
  induction d as [|d IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. etrans; [exact IH | apply sess_n_step].
Qed.

(* R3's monotonicity, both ways round *)
Lemma expected_rel_out_mono l out out' :
  out' `prefix_of` out -> expected_rel l out -> expected_rel l out'.
Proof.
  intros Hp (cs & Hcs & Hout). exists cs. split; [exact Hcs|]. by etrans.
Qed.

Lemma expected_rel_ins_mono l l' out :
  length l <= length l' -> expected_rel l out -> expected_rel l' out.
Proof.
  intros Hlen (cs & Hcs & Hout). exists cs. split; [exact Hcs|].
  etrans; [exact Hout|]. rewrite /sess. by apply sess_n_mono.
Qed.

Lemma expected_rel_ins_prefix l l' out :
  l `prefix_of` l' -> expected_rel l out -> expected_rel l' out.
Proof. intros Hp. apply expected_rel_ins_mono. by apply prefix_length. Qed.

(* ...and the decomposition D3 gives the session: under [star_prefix] the
   input really is [q] whole lines and a prefix of the next, which is why
   [sess_n] may read only the LENGTH of the input. *)
Lemma star_prefix_decomp (l : list (bv 8)) :
  star_prefix echo_line l ->
  l = concat (replicate (length l `div` length echo_line) echo_line)
      ++ take (length l `mod` length echo_line) echo_line.
Proof.
  intros Hsp.
  pose proof echo_line_length as HL.
  pose proof (Nat.div_mod_eq (length l) (length echo_line)) as Hdm.
  pose proof (Nat.mod_upper_bound (length l) (length echo_line)
                ltac:(lia)) as Hub.
  assert (Hqn : length l `div` length echo_line <= length l).
  { apply Nat.Div0.div_le_upper_bound. nia. }
  assert (Hsplit : replicate (length l) echo_line
                 = replicate (length l `div` length echo_line) echo_line
                   ++ replicate (length l - length l `div` length echo_line)
                        echo_line).
  { rewrite -replicate_add. f_equal. lia. }
  rewrite {1}Hsp Hsplit concat_app take_app.
  rewrite take_ge; [|rewrite concat_replicate_length; nia].
  rewrite concat_replicate_length. f_equal.
  replace (length l - length l `div` length echo_line * length echo_line)
    with (length l `mod` length echo_line) by nia.
  destruct (decide (length l `mod` length echo_line = 0)) as [Hr0|Hr0].
  { by rewrite Hr0 !take_0. }
  destruct (length l - length l `div` length echo_line) as [|d] eqn:Hd.
  { exfalso. nia. }
  rewrite replicate_S concat_cons take_app_le; [done|lia].
Qed.

(* ====================================================================== *)
(*  5.  D0 IS UNAMBIGUOUS: THE SESSION HAS NO DIGITS (R2)                  *)
(* ====================================================================== *)

Definition digit_bytes : list (bv 8) :=
  Z_to_bv 8 <$> [48;49;50;51;52;53;54;55;56;57]%Z.

Definition digit_free (w : list (bv 8)) : Prop :=
  Forall (fun b => b ∉ digit_bytes) w.

Global Instance digit_free_dec w : Decision (digit_free w).
Proof. unfold digit_free. apply _. Defined.

Lemma digit_free_app w1 w2 :
  digit_free w1 -> digit_free w2 -> digit_free (w1 ++ w2).
Proof. rewrite /digit_free Forall_app. by split. Qed.

Lemma digit_free_take n w : digit_free w -> digit_free (take n w).
Proof. rewrite /digit_free. apply Forall_take. Qed.

Lemma digit_free_sublist (l w : list (bv 8)) :
  l `sublist_of` w -> digit_free w -> digit_free l.
Proof.
  rewrite /digit_free.
  induction 1 as [| x l w _ IH | x l w _ IH]; intros Hw; [done| |].
  - rewrite Forall_cons in Hw. destruct Hw as [Hx Hw].
    rewrite Forall_cons. split; [exact Hx | by apply IH].
  - rewrite Forall_cons in Hw. by apply IH, Hw.
Qed.

Lemma digit_free_prefix (l w : list (bv 8)) :
  l `prefix_of` w -> digit_free w -> digit_free l.
Proof. intros [k ->]. rewrite /digit_free Forall_app. by intros [? _]. Qed.

(* the U side, byte for byte: no digit anywhere *)
Lemma digit_free_prologue : digit_free u_prologue.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma digit_free_echo_line : digit_free echo_line.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma digit_free_line_alts : Forall digit_free line_alts.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma digit_free_alt (c : nat) : digit_free (line_alts !!! c).
Proof.
  destruct (line_alts !! c) as [a|] eqn:E.
  - rewrite (list_lookup_total_correct _ _ _ E).
    by eapply Forall_lookup_1; [apply digit_free_line_alts|exact E].
  - rewrite list_lookup_total_alt E /=. constructor.
Qed.

Lemma digit_free_alt_seq cs q : digit_free (alt_seq cs q).
Proof.
  induction q as [|q IH].
  - rewrite alt_seq_0. constructor.
  - rewrite alt_seq_S. apply digit_free_app; [exact IH|].
    rewrite /alt_blk. apply digit_free_app;
      [apply digit_free_echo_line | apply digit_free_alt].
Qed.

Lemma digit_free_sess_n cs n : digit_free (sess_n cs n).
Proof.
  rewrite /sess_n. apply digit_free_app; [apply digit_free_prologue|].
  apply digit_free_app;
    [apply digit_free_alt_seq | apply digit_free_take, digit_free_echo_line].
Qed.

(* ...while every hart line carries its own decimal digit *)
Lemma hart_lines_not_digit_free (l : list (bv 8)) :
  l ∈ hart_lines -> ~ digit_free l.
Proof.
  intros Hl.
  assert (HF : Forall (fun m => ~ digit_free m) hart_lines).
  { apply (bool_decide_unpack _). vm_compute. exact I. }
  rewrite Forall_forall in HF. by apply HF.
Qed.

(* D0'S UNAMBIGUITY.  No hart line is a subsequence of anything the session
   can have printed, so the point at which the discipline lets the user
   start typing cannot be faked by the user's own transcript. *)
Lemma k_done_digit_free (w : list (bv 8)) : digit_free w -> ~ k_done w.
Proof.
  intros Hdf Hk.
  assert (Hin : hart_line 1%Z ∈ hart_lines).
  { rewrite /hart_lines. apply elem_of_list_fmap_1, elem_of_list_here. }
  apply (hart_lines_not_digit_free _ Hin).
  eapply digit_free_sublist; [|exact Hdf].
  rewrite /k_done Forall_forall in Hk. by apply Hk.
Qed.

Lemma hart_line_not_sublist_sess (cs : list nat) (n : nat)
    (l w : list (bv 8)) :
  l ∈ hart_lines -> w `prefix_of` sess_n cs n -> ~ (l `sublist_of` w).
Proof.
  intros Hl Hw Hs. apply (hart_lines_not_digit_free _ Hl).
  eapply digit_free_sublist; [exact Hs|].
  eapply digit_free_prefix; [exact Hw | apply digit_free_sess_n].
Qed.

Lemma k_point_sess_n (cs : list nat) (n : nat) : k_point (sess_n cs n) = None.
Proof.
  apply k_point_None. intros k _. apply k_done_digit_free.
  apply digit_free_take, digit_free_sess_n.
Qed.

Lemma k_point_expected (l out : list (bv 8)) :
  expected_rel l out -> k_point out = None.
Proof.
  intros (cs & _ & Hp). apply k_point_None. intros k _.
  apply k_done_digit_free, digit_free_take.
  eapply digit_free_prefix; [exact Hp | apply digit_free_sess_n].
Qed.

(* ====================================================================== *)
(*  6.  THE DISCIPLINE (R4)                                               *)
(* ====================================================================== *)

(* the wire the user had seen when each input byte was typed: [in_pres seg]
   lists, in order, the prefix of [seg] STRICTLY BEFORE its i-th
   [ObsUartIn]. *)
Fixpoint in_pres (seg : list mobs) : list (list mobs) :=
  match seg with
  | [] => []
  | ObsUartIn b :: seg' => [] :: ((fun p => ObsUartIn b :: p) <$> in_pres seg')
  | e :: seg' => (fun p => e :: p) <$> in_pres seg'
  end.

Lemma in_pres_length seg : length (in_pres seg) = length (ins seg).
Proof.
  induction seg as [|e seg IH]; [done|].
  destruct e; cbn; rewrite ?length_fmap IH //.
Qed.

Lemma in_pres_out seg b : in_pres (seg ++ [ObsUartOut b]) = in_pres seg.
Proof. induction seg as [|e seg IH]; [done|]. destruct e; cbn; rewrite IH //. Qed.

Lemma in_pres_in seg b : in_pres (seg ++ [ObsUartIn b]) = in_pres seg ++ [seg].
Proof.
  induction seg as [|e seg IH]; [done|].
  destruct e; cbn; rewrite IH ?fmap_app //.
Qed.

(* D0 AND D1/D2 AT ONE INPUT POSITION.  [p] is the wire before input [i]:
     D0    every hart line has already appeared in it, so what follows the
           k-point is PURE U;
     D1/D2 the whole expected transcript for the [i] bytes typed so far is
           already there, after the k-point.  Mid-line that transcript ends
           in the echo of byte [i-1] (D2); at a line boundary it ends in
           the "$ " of the previous line's continuation (D1). *)
Definition disc_pt (cs : list nat) (i : nat) (p : list mobs) : Prop :=
  k_done (obs_wire p)
  /\ sess_n cs i `prefix_of` drop (k_pt (obs_wire p)) (obs_wire p).

Global Instance disc_pt_dec cs i p : Decision (disc_pt cs i p).
Proof. rewrite /disc_pt. apply _. Qed.

(* THE NEW PER-CYCLE DISCIPLINE: D3, and at every input byte D0 + D1/D2
   under ONE resolution of the per-line alternatives. *)
Definition disc_seg' (seg : list mobs) : Prop :=
  disc_seg seg
  /\ exists cs : list nat,
       length cs = length (ins seg) `div` length echo_line
       /\ Forall (fun c => c < length line_alts) cs
       /\ forall (i : nat) (p : list mobs),
            in_pres seg !! i = Some p -> disc_pt cs i p.

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
  - rewrite elem_of_list_singleton. split.
    + intros ->. split; [done|constructor].
    + intros [Hl _]. by apply nil_length_inv.
  - rewrite elem_of_list_fmap. split.
    + intros ([c cs'] & -> & Hp). cbn.
      apply elem_of_list_In in Hp. apply in_prod_iff in Hp as [Hc Hcs].
      apply in_seq in Hc. apply elem_of_list_In in Hcs.
      apply IH in Hcs as [Hl Hf].
      split; [by rewrite /= Hl|]. rewrite Forall_cons. split; [lia|exact Hf].
    + intros [Hl Hf]. destruct cs as [|c cs']; [done|].
      rewrite Forall_cons in Hf. destruct Hf as [Hc Hf].
      exists (c, cs'). split; [done|].
      apply elem_of_list_In, in_prod_iff. split.
      * apply in_seq. lia.
      * apply elem_of_list_In, IH. split; [by injection Hl|exact Hf].
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

Global Instance disc_seg'_dec seg : Decision (disc_seg' seg).
Proof.
  rewrite /disc_seg'.
  destruct (decide (disc_seg seg)) as [Hd|Hd]; [|right; by intros [? _]].
  destruct (decide (Exists (fun cs => Forall (fun ip => disc_pt cs ip.1 ip.2)
                                        (imap (fun i x => (i, x)) (in_pres seg)))
             (bounded_lists (length line_alts)
                (length (ins seg) `div` length echo_line)))) as [HE|HE].
  - left. split; [exact Hd|].
    apply Exists_exists in HE as (cs & Hcs & HF).
    apply elem_of_bounded_lists in Hcs as [Hl Hf].
    exists cs. split; [exact Hl|]. split; [exact Hf|].
    by apply Forall_imap_pair.
  - right. intros [_ (cs & Hl & Hf & Hall)]. apply HE.
    apply Exists_exists. exists cs. split.
    + apply elem_of_bounded_lists. by split.
    + by apply Forall_imap_pair.
Qed.

Lemma disc_seg'_nil : disc_seg' [].
Proof.
  split; [exact disc_seg_nil|]. exists []. split; [done|].
  split; [constructor|]. intros i p Hi.
  apply lookup_lt_Some in Hi. cbn in Hi. lia.
Qed.

(* THE PROJECTION.  Everything the tree already proves against the landed
   discipline reads off the new one in one step. *)
Lemma disc_seg'_proj seg : disc_seg' seg -> disc_seg seg.
Proof. by intros [? _]. Qed.

(* THE DISCIPLINE, over the WHOLE history (uart-trace.md ruling 1): every
   cycle's input keeps the rate discipline.  [cycles_of h] lists every
   cycle, the open one LAST while the power is on, so the open cycle is
   covered. *)
Definition disc (h : list mobs) : Prop := Forall disc_seg' (cycles_of h).

Global Instance disc_dec h : Decision (disc h).
Proof. rewrite /disc. apply _. Qed.

Lemma disc_nil : disc [].
Proof. constructor. Qed.

Lemma disc_proj h : disc h -> disc_old h.
Proof.
  rewrite /disc /disc_old. intros H. apply Forall_lookup. intros i seg Hi.
  apply disc_seg'_proj. by eapply Forall_lookup_1.
Qed.

(* ---- the three closure laws, at the SAME statements they had ---- *)

Lemma disc_seg'_out (seg : list mobs) (b : bv 8) :
  disc_seg' (seg ++ [ObsUartOut b]) <-> disc_seg' seg.
Proof.
  assert (Hi : in_pres (seg ++ [ObsUartOut b]) = in_pres seg)
    by apply in_pres_out.
  assert (Hn : ins (seg ++ [ObsUartOut b]) = ins seg)
    by (rewrite ins_app ins_out app_nil_r; reflexivity).
  rewrite /disc_seg' /disc_seg Hi Hn. done.
Qed.

Lemma disc_out (h : list mobs) (b : bv 8) :
  trace_shape h true ->
  disc (h ++ [ObsUartOut b]) <-> disc h.
Proof.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartOut b] Hsh) as (cs & Hc & Hc');
    [by constructor|].
  rewrite /disc Hc Hc' !Forall_app !Forall_singleton disc_seg'_out. done.
Qed.

Lemma disc_power (h : list mobs) (on : bool) :
  disc (h ++ [if on then ObsPowerOff else ObsPowerOn]) <-> disc h.
Proof.
  rewrite /disc. destruct on.
  - by rewrite cycles_of_off.
  - rewrite cycles_of_on Forall_app Forall_singleton.
    split; [by intros [? _] | intros ?; split; [done | exact disc_seg'_nil]].
Qed.

(* an input byte can only have BROKEN the discipline: the witness for the
   shorter history is the longer one's choice list, cut to the lines the
   shorter input completed. *)
Lemma alt_seq_ext cs1 cs2 q :
  (forall j, j < q -> cs1 !!! j = cs2 !!! j) -> alt_seq cs1 q = alt_seq cs2 q.
Proof.
  induction q as [|q IH]; intros Hj; [done|].
  rewrite !alt_seq_S IH; [|intros j Hjq; apply Hj; lia].
  rewrite /alt_blk (Hj q ltac:(lia)) //.
Qed.

Lemma sess_n_take cs n q :
  n `div` length echo_line <= q -> sess_n (take q cs) n = sess_n cs n.
Proof.
  intros Hq. rewrite /sess_n. do 2 f_equal.
  apply alt_seq_ext. intros j Hj.
  rewrite list_lookup_total_alt lookup_take; [|lia].
  by rewrite -list_lookup_total_alt.
Qed.

Lemma disc_seg'_in (seg : list mobs) (b : bv 8) :
  disc_seg' (seg ++ [ObsUartIn b]) -> disc_seg' seg.
Proof.
  intros [Hd (cs & Hl & Hf & Hall)].
  rewrite /disc_seg ins_app ins_in in Hd.
  rewrite ins_app ins_in length_app /= in Hl.
  split; [exact (star_prefix_snoc _ _ _ echo_line_pos Hd)|].
  exists (take (length (ins seg) `div` length echo_line) cs).
  split.
  { assert (H1 : length (ins seg) `div` length echo_line
                 <= (length (ins seg) + 1) `div` length echo_line)
      by (apply Nat.Div0.div_le_mono; lia).
    rewrite length_take Hl Nat.min_l; [done|exact H1]. }
  split; [by apply Forall_take|].
  intros i p Hi.
  assert (Hlt : i < length (ins seg)).
  { apply lookup_lt_Some in Hi. by rewrite in_pres_length in Hi. }
  assert (Hi' : in_pres (seg ++ [ObsUartIn b]) !! i = Some p).
  { rewrite in_pres_in lookup_app_l; [exact Hi|].
    rewrite in_pres_length. lia. }
  destruct (Hall i p Hi') as [Hk Hpre].
  split; [exact Hk|].
  rewrite sess_n_take; [exact Hpre|].
  apply Nat.Div0.div_le_mono. lia.
Qed.

Lemma disc_in (h : list mobs) (b : bv 8) :
  trace_shape h true ->
  disc (h ++ [ObsUartIn b]) -> disc h.
Proof.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartIn b] Hsh) as (cs & Hc & Hc');
    [by constructor|].
  rewrite /disc Hc Hc' !Forall_app !Forall_singleton.
  intros [Hall Hseg]. split; [exact Hall|]. exact (disc_seg'_in _ _ Hseg).
Qed.

(* ====================================================================== *)
(*  7.  THE CLAIM (R5)                                                    *)
(* ====================================================================== *)

(* an INTERLEAVING of two streams, order preserved within each.  The wire
   carries no source tag ([RiscvLang.mobs] has only the byte), so the claim
   says the observed bytes ARE such an interleaving -- and the witness is
   the kernel's own per-byte tagging (lane TX-TAG), never chosen for
   convenience. *)
Inductive shuffle {A} : list A -> list A -> list A -> Prop :=
  | shuffle_nil : shuffle [] [] []
  | shuffle_l (x : A) l1 l2 l : shuffle l1 l2 l -> shuffle (x :: l1) l2 (x :: l)
  | shuffle_r (x : A) l1 l2 l : shuffle l1 l2 l -> shuffle l1 (x :: l2) (x :: l).

Lemma shuffle_nil_l {A} (l : list A) : shuffle [] l l.
Proof. induction l; by constructor. Qed.
Lemma shuffle_nil_r {A} (l : list A) : shuffle l [] l.
Proof. induction l; by constructor. Qed.
Lemma shuffle_length {A} (l1 l2 l : list A) :
  shuffle l1 l2 l -> length l = length l1 + length l2.
Proof. induction 1; cbn; lia. Qed.

(* THE KERNEL STREAM.  printk holds pr.lock for a whole message, so the ten
   boot messages do not interleave with each other; hart 0's three precede
   [started = 1] and so precede all seven hart lines, which the scheduler
   may order any way it likes.  The trace may stop in the middle of one,
   hence the prefix. *)
Definition boot_stream (ks : list (bv 8)) : Prop :=
  exists hl : list (list (bv 8)),
    hl ≡ₚ hart_lines
    /\ ks `prefix_of` (msg_nl ++ msg_booting ++ msg_nl ++ concat hl).

(* THE OUTPUT CLAIM for one power cycle: every byte that reached the wire
   is either a boot message's or the session's, in each one's own order,
   and the session part is a PREFIX of the transcript this cycle's input
   calls for. *)
Definition good_out (seg : list mobs) : Prop :=
  exists (cs : list nat) (ks us : list (bv 8)),
    shuffle ks us (obs_wire seg)
    /\ boot_stream ks
    /\ us `prefix_of` sess cs (ins seg).

Lemma good_out_nil : good_out [].
Proof.
  exists [], [], []. split; [constructor|]. split.
  - exists hart_lines. split; [done|]. apply prefix_nil.
  - apply prefix_nil.
Qed.
