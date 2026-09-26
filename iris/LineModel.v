(* ===================================================================== *)
(*  LineModel.v -- THE LINE MODEL, once (app-both milestone M1).           *)
(*                                                                       *)
(*  The three applications' expected-session transcripts                  *)
(*  ([EchoDisc.sess], [FileDisc.sessf], [PipeDisc.sessp]) are ONE fold:   *)
(*                                                                       *)
(*     prologue(ps) ++ concat (block i, i < nlines I) ++ rest_of I         *)
(*     block i := body_i ++ NL ++ cont  (state_i) (line_i) (alt_i)       *)
(*               ++ (the next prologue round, at a MAIN-loop fork panic)  *)
(*                                                                       *)
(*  where the STATE is threaded through the blocks by the model's step    *)
(*  ([FileDisc.fsm] at the file; the identity at echo and at the          *)
(*  pipeline, whose state is [unit]).  What an application supplies is    *)
(*  the record below -- its lines, its alternatives with their code and   *)
(*  their panic bit, its continuation bytes at a state, its step -- and   *)
(*  everything the discipline, the claim families and the determinacy    *)
(*  argument read off the transcript is stated here over the record.      *)
(*                                                                       *)
(*  M1's exit: the three landed sessions are this fold at their instance *)
(*  ([LineModelInst.v]: [sessf_lm], [sessp_lm], [sess_lm]), so that the   *)
(*  generic families (M2) can be stated at [lm_sess] and every landed     *)
(*  statement recovered by rewriting with the equation.                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.        (* [bodies_of], [rest_of], [nlines], [nstarted], [wl_nl] *)
Require Import EchoDisc.         (* [pro_of], [pro_from], [pro_rounds], [pro_alts], [in_pres] *)
Require Import LineBytes.        (* [nodollar], the '$'-split, the panic collision *)
(* AFTER the three above, so the library load order is unchanged for every
   file above this one ([EchoDisc] already loads both) *)
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [obs_wire Uart0], [cycles_of] *)
From stdpp Require Import ssreflect.

Local Open Scope nat_scope.

(* ====================================================================== *)
(*  1.  THE RECORD                                                         *)
(* ====================================================================== *)
Record lmodel := MkLM {
  (* the state a round leaves for the next: the file's content at the file
     application, [unit] where no line touches the file system *)
  lm_st : Type;
  (* the line, as a complete body parses to it -- total, at a default the
     discipline never lets happen ([FileDisc.uline_of]'s shape) *)
  lm_line : Type;
  lm_of : list (bv 8) -> lm_line;
  (* the alternatives that decide a round, DECODED from the stage's code
     ([cs !!! i]); the code is what the era's [cs_auth]/[cs_lb] carry *)
  lm_alt : Type;
  lm_dec : nat -> lm_alt;
  (* the MAIN-loop fork panic: the shell died, init restarts it, and the
     next prologue round follows the panic's bytes *)
  lm_panic : lm_alt -> bool;
  (* the continuation the console shows for the round, at the state the
     round starts in; and the state it leaves *)
  lm_cont : lm_st -> lm_line -> lm_alt -> list (bv 8);
  lm_step : lm_st -> lm_line -> lm_alt -> lm_st;
  (* which alternatives a line admits at the state its round starts in
     (the range condition the stage's choice list is checked against) *)
  lm_ok : lm_st -> lm_line -> lm_alt -> Prop;
  (* THE INPUT DISCIPLINE's two readings of a body: a complete body parses
     to an admissible line; a partial one is body bytes *)
  lm_body_ok : list (bv 8) -> Prop;
  lm_body_byte : bv 8 -> Prop;
  (* the well-formed lines (what a complete body parses to) and the states
     the rounds keep the application in *)
  lm_line_ok : lm_line -> Prop;
  lm_st_ok : lm_st -> Prop;
  (* THE COVERAGE-ENDING ARM: an alternative after which the discipline
     reads nothing more of the era (the pipeline's fork failure at the
     second child, [PipeDisc.PForkS]); [false] everywhere else *)
  lm_term : lm_alt -> bool;
  (* the outputs such an arm can have put on the wire AT A LINE, closed
     under prefix ([PipeDisc.pmergeable]); [False] where no arm ends
     coverage.  LINE-INDEXED (seccomp design section 3): at a line whose
     terminal arm's continuation is ANY byte string (the union's
     [seccomp x]) it is [True] there, while at a pipeline it stays the
     pipeline's own set -- a line-free reading would make every pipeline
     round mergeable.  The determinacy argument compares two witnesses at
     ONE line, so nothing else changes. *)
  lm_merge : lm_line -> list (bv 8) -> Prop;
}.

(* WHAT FOLLOWS SH'S PANIC LINE ON THE WIRE: init's next prologue round,
   settled ([pro_done]) with anything after it, or cut short by the end of
   the wire ([W = []]).  An output below one wire with the panic line is
   compared only against THIS -- the continuation [lm_cont_all] actually
   puts after a panic -- and not against every byte string: the owner's
   ruling (2026-09-24) lets a line's output look like the panic line
   followed by anything else (the pipeline's [echo fork | cat | cat] with a
   middle cat's write error), since the output need not parse unambiguously. *)
Definition lm_below_panic (u Y : list (bv 8)) (ps : list nat) (W : list (bv 8)) : Prop :=
  ((W = [] \/ pro_done ps)
   /\ (u ++ u_prompt ++ Y) `prefix_of` (alt_panic ++ pro_of ps ++ W))
  \/ (pro_done ps /\ (alt_panic ++ pro_of ps ++ W) `prefix_of` (u ++ u_prompt ++ Y)).

(* ...which is one of the comparisons against an arbitrary continuation *)
Lemma lm_below_panic_any u Y ps W :
  lm_below_panic u Y ps W ->
  ((u ++ u_prompt ++ Y) `prefix_of` (alt_panic ++ (pro_of ps ++ W))
   \/ (alt_panic ++ (pro_of ps ++ W)) `prefix_of` (u ++ u_prompt ++ Y)).
Proof using. intros [[_ H] | [_ H]]; [left | right]; exact H. Qed.

(* THE BYTE SHAPE OF A MODEL, which is all the determinacy argument reads
   off it: a panicking alternative prints sh's panic line; every other one
   prints a '$'-free run then the prompt, and put beside the panic line
   AND THE PROLOGUE INIT PRINTS AFTER IT on one wire IS the panic line
   ([lm_below_panic]: beside the panic line followed by anything else it
   may be anything); a coverage-ending alternative never panics,
   its output is a mergeable one, and the discipline's coverage-ending
   guard refutes a mergeable output at its own side. *)
Record lm_laws (M : lmodel) : Prop := MkLML {
  lml_body_line : forall b, lm_body_ok M b -> lm_line_ok M (lm_of M b);
  lml_st_step : forall s l a,
    lm_st_ok M s -> lm_line_ok M l -> lm_ok M s l a -> lm_st_ok M (lm_step M s l a);
  lml_cont_panic : forall s l a, lm_panic M a = true -> lm_cont M s l a = alt_panic;
  lml_term_nopanic : forall a, lm_term M a = true -> lm_panic M a = false;
  lml_term_merge : forall s l a,
    lm_st_ok M s -> lm_ok M s l a -> lm_term M a = true -> lm_merge M l (lm_cont M s l a);
  lml_merge_prefix : forall l u' u, u' `prefix_of` u -> lm_merge M l u -> lm_merge M l u';
  lml_cont_shape : forall s l a,
    lm_st_ok M s -> lm_line_ok M l -> lm_ok M s l a ->
    lm_panic M a = false -> lm_term M a = false ->
    exists u, lm_cont M s l a = u ++ u_prompt
              /\ Forall nodollar u
              /\ (forall Y ps W,
                    Forall (fun x => x < length pro_alts) ps ->
                    lm_below_panic u Y ps W -> u = alt_panic);
  (* a line that admits a coverage-ending alternative at one state admits
     one at every state: what moves the D4 guard's evidence between the
     two witnesses' states in the determinacy argument *)
  lml_term_st : forall s l c,
    lm_ok M s l c -> lm_term M c = true ->
    forall s', exists c', lm_ok M s' l c' /\ lm_term M c' = true;
}.
Arguments lml_body_line {M} _.
Arguments lml_st_step {M} _.
Arguments lml_cont_panic {M} _.
Arguments lml_term_nopanic {M} _.
Arguments lml_term_merge {M} _.
Arguments lml_merge_prefix {M} _.
Arguments lml_cont_shape {M} _.
Arguments lml_term_st {M} _.

(* THE BYTE LAWS: what the discipline says of a line's bytes, at the
   model.  Separate from [lm_laws] (the byte SHAPE of continuations) so
   that an instance can have the one without the other -- echo's model has
   no [lm_laws] record in the landed tree.  Every instance proves the four
   in a line each: a well-formed body is made of body bytes, is shorter
   than the line buffer, a body byte is printable (which is what refutes
   the carriage return, the erase bytes and ^D at once), and the
   out-of-range reading of a choice list ([lm_dec M 0]) never panics. *)
Record lm_byte_laws (M : lmodel) : Prop := MkLMB {
  lmb_body_bytes : forall l, lm_body_ok M l -> Forall (lm_body_byte M) l;
  lmb_body_short : forall l, lm_body_ok M l -> S (length l) < line_max;
  lmb_byte_printable : forall b, lm_body_byte M b -> (32 <= bv_unsigned b < 127)%Z;
  lmb_dec0_nopanic : lm_panic M (lm_dec M 0) = false;
}.
Arguments lmb_body_bytes {M} _.
Arguments lmb_body_short {M} _.
Arguments lmb_byte_printable {M} _.
Arguments lmb_dec0_nopanic {M} _.

Section line_model.
  Context (M : lmodel).

  (* the round's alternative, read off the stage *)
  Definition lm_at (cs : list nat) (i : nat) : lm_alt M := lm_dec M (cs !!! i).

  (* THE ROUND POINTER: how many shells have died on their own main-loop
     fork panic before line [i] -- one prologue round each *)
  Fixpoint lm_pro_idx (cs : list nat) (i : nat) : nat :=
    match i with
    | 0 => 0
    | S i' => lm_pro_idx cs i' + if lm_panic M (lm_at cs i') then 1 else 0
    end.

  (* THE STATE BEFORE ROUND [q]: the boot state, moved by every round
     before it *)
  Fixpoint lm_upto (cs : list nat) (s : lm_st M) (bs : list (list (bv 8)))
      (q : nat) : lm_st M :=
    match q with
    | 0 => s
    | S q' => lm_step M (lm_upto cs s bs q') (lm_of M (bs !!! q')) (lm_at cs q')
    end.

  (* the console continuation of round [i], with the next prologue round
     after a panic *)
  Definition lm_cont_at (ps cs : list nat) (s : lm_st M)
      (bs : list (list (bv 8))) (i : nat) : list (bv 8) :=
    lm_cont M (lm_upto cs s bs i) (lm_of M (bs !!! i)) (lm_at cs i)
    ++ (if lm_panic M (lm_at cs i)
        then pro_of (pro_from (S (lm_pro_idx cs i)) ps) else []).

  (* the round's block: the echoed line, its newline, its continuation *)
  Definition lm_blk (ps cs : list nat) (s : lm_st M)
      (bs : list (list (bv 8))) (i : nat) : list (bv 8) :=
    bs !!! i ++ wl_nl :: lm_cont_at ps cs s bs i.

  Definition lm_seq (ps cs : list nat) (s : lm_st M)
      (bs : list (list (bv 8))) (q : nat) : list (bv 8) :=
    concat (lm_blk ps cs s bs <$> List.seq 0 q).

  (* THE EXPECTED SESSION TRANSCRIPT for the era's input [I] at boot
     state [s] *)
  Definition lm_sess (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
    : list (bv 8) :=
    pro_of ps ++ lm_seq ps cs s (bodies_of I) (nlines I) ++ rest_of I.

  (* the state after the last COMPLETE line of [I] *)
  Definition lm_after (cs : list nat) (s : lm_st M) (I : list (bv 8))
    : lm_st M :=
    lm_upto cs s (bodies_of I) (nlines I).

  (* ---- the prologue's range and pin, as every instance states them ---- *)
  Definition lm_pro_ok (ps cs : list nat) (q : nat) : Prop :=
    Forall (fun a => a < length pro_alts) ps
    /\ lm_pro_idx cs q < pro_rounds ps.

  Definition lm_pro_pin (ps cs : list nat) (I : list (bv 8)) : Prop :=
    forall q, q < nstarted I -> lm_pro_idx cs q < pro_rounds ps.

  (* ---- the stage's range condition and the input discipline: one
          entry per complete line, each checked at the state ITS round
          starts in ---- *)
  Definition lm_alts_ok (s : lm_st M) (I : list (bv 8)) (cs : list nat) : Prop :=
    length cs = nlines I
    /\ forall i, i < nlines I ->
         lm_ok M (lm_upto cs s (bodies_of I) i) (lm_of M (bodies_of I !!! i))
           (lm_at cs i).

  Definition lm_disc_input (I : list (bv 8)) : Prop :=
    Forall (lm_body_ok M) (bodies_of I)
    /\ Forall (lm_body_byte M) (rest_of I)
    /\ S (length (rest_of I)) < line_max.

  (* ---- THE STREAM the writer walks: what is pending after the input so
          far, and what was due before each byte of it ---- *)
  Definition lm_pending_at (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
    : list (bv 8) :=
    if decide (I = []) then pro_of ps
    else if decide (rest_of I = [])
         then lm_cont_at ps cs s (bodies_of I) (nlines I - 1) else [].

  Fixpoint lm_proc_before_from (ps cs : list nat) (s : lm_st M)
      (pre I : list (bv 8)) : list (bv 8) :=
    match I with
    | [] => []
    | b :: I' => lm_pending_at ps cs s pre
                 ++ lm_proc_before_from ps cs s (pre ++ [b]) I'
    end.

  Definition lm_proc_before (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
    : list (bv 8) := lm_proc_before_from ps cs s [] I.

  Definition lm_proc_stream (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
    : list (bv 8) :=
    lm_proc_before ps cs s I ++ lm_pending_at ps cs s I.

  (* ---- THE WRITER'S STAGES, as every console family names them ---- *)
  Definition lm_wr_pro (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_pro_pin ps cs I
    /\ rest_of I = []
    /\ nlines I = length cs
    /\ (I = [] \/ lm_panic M (lm_at cs (nlines I - 1)) = true)
    /\ ~ pro_done (pro_from (lm_pro_idx cs (nlines I)) ps)
    /\ P = length (lm_proc_stream ps cs s I).

  Definition lm_wr_blk (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_pro_pin ps cs I
    /\ rest_of I = []
    /\ nlines I = S (length cs)
    /\ P = length (lm_proc_before ps cs s I).

  Definition lm_wr_open (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_pro_pin ps cs I
    /\ rest_of I = []
    /\ nlines I = length cs
    /\ lm_pro_idx cs (nlines I) < pro_rounds ps
    /\ P = length (lm_proc_stream ps cs s I).

  Definition lm_wr_owed (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_wr_pro ps cs s I P \/ lm_wr_blk ps cs s I P.

  Definition lm_wr_sp (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_wr_open ps cs s I (S P)
    /\ lm_proc_stream ps cs s I !! P = Some (u_prompt !!! 1).

  (* the banner-owed cursor stands after the OPEN round's [j] failed
     sub-rounds; the pre-bytes are the panic's when a line was typed *)
  Definition lm_wr_pre (I : list (bv 8)) : list (bv 8) :=
    if decide (I = []) then [] else alt_panic.

  Definition lm_wr_ban (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P : nat) : Prop :=
    lm_pro_pin ps cs I
    /\ rest_of I = []
    /\ nlines I = length cs
    /\ (I = [] \/ lm_panic M (lm_at cs (nlines I - 1)) = true)
    /\ (exists j : nat,
          pro_from (lm_pro_idx cs (nlines I)) ps = pro_fail j
          /\ P = length (lm_proc_before ps cs s I) + length (lm_wr_pre I)
                 + pro_round * j).

  Definition lm_wr_tail (ps cs : list nat) : Prop :=
    pro_from (S (lm_pro_idx cs (length cs))) ps = [].

  Definition lm_wr_blk_t ps cs s I P : Prop := lm_wr_blk ps cs s I P /\ lm_wr_tail ps cs.
  Definition lm_wr_sp_t ps cs s I P : Prop := lm_wr_sp ps cs s I P /\ lm_wr_tail ps cs.
  Definition lm_wr_open_t ps cs s I P : Prop := lm_wr_open ps cs s I P /\ lm_wr_tail ps cs.

  Definition lm_wr_banp (ps cs : list nat) (s : lm_st M) (I : list (bv 8))
      (P i : nat) : Prop :=
    match i with
    | O => lm_wr_ban ps cs s I P
    | S _ => exists ps' : list nat, ps = ps' ++ [3] /\ lm_wr_ban ps' cs s I P
    end.

  (* the choice list of a block with [i] bytes out: the first byte files it *)
  Definition lm_blkcs (cs : list nat) (a i : nat) : list nat :=
    match i with O => cs | S _ => cs ++ [a] end.

  (* ---- structure ---- *)
  Lemma lm_seq_0 ps cs s bs : lm_seq ps cs s bs 0 = [].
  Proof using. reflexivity. Qed.

  Lemma lm_seq_S ps cs s bs q :
    lm_seq ps cs s bs (S q) = lm_seq ps cs s bs q ++ lm_blk ps cs s bs q.
  Proof using.
    rewrite /lm_seq seq_S fmap_app concat_app /=. by rewrite app_nil_r.
  Qed.

  Lemma lm_sess_nil ps cs s : lm_sess ps cs s [] = pro_of ps.
  Proof using.
    rewrite /lm_sess rest_of_nil nlines_nil lm_seq_0. by rewrite !app_nil_r.
  Qed.

  (* the round pointer, step by step *)
  Lemma lm_pro_idx_S cs i :
    lm_pro_idx cs (S i)
    = lm_pro_idx cs i + if lm_panic M (lm_at cs i) then 1 else 0.
  Proof using. reflexivity. Qed.

  Lemma lm_pro_idx_Sp cs i :
    lm_panic M (lm_at cs i) = true -> lm_pro_idx cs (S i) = S (lm_pro_idx cs i).
  Proof using. intro H. rewrite lm_pro_idx_S H. lia. Qed.

  Lemma lm_pro_idx_Sn cs i :
    lm_panic M (lm_at cs i) = false -> lm_pro_idx cs (S i) = lm_pro_idx cs i.
  Proof using. intro H. rewrite lm_pro_idx_S H. lia. Qed.

  Lemma lm_pro_idx_mono cs i j : i <= j -> lm_pro_idx cs i <= lm_pro_idx cs j.
  Proof using.
    intros Hij. induction j as [| j IH].
    - assert (i = 0) by lia. by subst i.
    - destruct (decide (i = S j)) as [-> | Hne]; [done |].
      rewrite lm_pro_idx_S.
      assert (lm_pro_idx cs i <= lm_pro_idx cs j) by (apply IH; lia).
      destruct (lm_panic M (lm_at cs j)); lia.
  Qed.

  Lemma lm_pro_idx_add cs n i :
    lm_pro_idx cs (n + i) = lm_pro_idx cs n + lm_pro_idx (drop n cs) i.
  Proof using.
    induction i as [| i IH]; [rewrite Nat.add_0_r; cbn [lm_pro_idx]; lia |].
    rewrite Nat.add_succ_r !lm_pro_idx_S IH /lm_at lb_lookup_total_drop.
    destruct (lm_panic M (lm_dec M (cs !!! (n + i)))); lia.
  Qed.

  (* the state, the continuation and the block after a drop *)
  Lemma lm_upto_drop cs s bs n i :
    lm_upto (drop n cs) (lm_upto cs s bs n) (drop n bs) i = lm_upto cs s bs (n + i).
  Proof using.
    induction i as [| i IH]; [by rewrite Nat.add_0_r |].
    rewrite Nat.add_succ_r. cbn [lm_upto]. rewrite IH.
    by rewrite /lm_at !lb_lookup_total_drop.
  Qed.

  Lemma lm_cont_at_drop ps cs s bs n i :
    lm_cont_at (pro_from (lm_pro_idx cs n) ps) (drop n cs) (lm_upto cs s bs n)
      (drop n bs) i
    = lm_cont_at ps cs s bs (n + i).
  Proof using.
    rewrite /lm_cont_at !lb_lookup_total_drop /lm_at !lb_lookup_total_drop.
    rewrite lm_upto_drop. f_equal.
    destruct (lm_panic M (lm_dec M (cs !!! (n + i)))); [| reflexivity].
    rewrite pro_from_add lm_pro_idx_add. f_equal. f_equal. lia.
  Qed.

  Lemma lm_blk_drop ps cs s bs n i :
    lm_blk (pro_from (lm_pro_idx cs n) ps) (drop n cs) (lm_upto cs s bs n)
      (drop n bs) i
    = lm_blk ps cs s bs (n + i).
  Proof using. by rewrite /lm_blk lb_lookup_total_drop lm_cont_at_drop. Qed.

  Lemma lm_seq_cons ps cs s bs q :
    lm_seq ps cs s bs (S q)
    = lm_blk ps cs s bs 0
      ++ lm_seq (pro_from (lm_pro_idx cs 1) ps) (drop 1 cs)
           (lm_upto cs s bs 1) (drop 1 bs) q.
  Proof using.
    rewrite /lm_seq.
    replace (List.seq 0 (S q)) with (0 :: List.seq 1 q) by reflexivity.
    rewrite fmap_cons concat_cons. f_equal.
    rewrite -List.seq_shift -list_fmap_compose.
    f_equal. apply list_fmap_ext.
    intros i x Hx. rewrite /compose. by rewrite (lm_blk_drop ps cs s bs 1 x).
  Qed.

  Lemma lm_seq_cons_assoc ps cs s bs q (t : list (bv 8)) :
    lm_seq ps cs s bs (S q) ++ t
    = bs !!! 0
      ++ wl_nl :: (lm_cont_at ps cs s bs 0
                   ++ (lm_seq (pro_from (lm_pro_idx cs 1) ps) (drop 1 cs)
                         (lm_upto cs s bs 1) (drop 1 bs) q ++ t)).
  Proof using. rewrite lm_seq_cons /lm_blk. apply lb_app4. Qed.

  (* the block reads the bodies only below its own index *)
  Lemma lm_upto_bs_ext cs s bs1 bs2 q :
    (forall j, j < q -> bs1 !!! j = bs2 !!! j) ->
    lm_upto cs s bs1 q = lm_upto cs s bs2 q.
  Proof using.
    induction q as [| q IH]; intros Hb; [reflexivity |].
    cbn [lm_upto]. rewrite (IH ltac:(intros j Hj; apply Hb; lia)).
    by rewrite (Hb q ltac:(lia)).
  Qed.

  Lemma lm_seq_bs_ext ps cs s bs1 bs2 q :
    (forall j, j < q -> bs1 !!! j = bs2 !!! j) ->
    lm_seq ps cs s bs1 q = lm_seq ps cs s bs2 q.
  Proof using.
    induction q as [| q IH]; intros Hb; [reflexivity |].
    rewrite !lm_seq_S (IH ltac:(intros j Hj; apply Hb; lia)). f_equal.
    rewrite /lm_blk /lm_cont_at (Hb q ltac:(lia)).
    by rewrite (lm_upto_bs_ext cs s bs1 bs2 q ltac:(intros j Hj; apply Hb; lia)).
  Qed.

  (* one round's continuation with the prologue it may re-enter *)
  Definition lm_cont_all (ps : list nat) (s : lm_st M) (l : lm_line M)
      (a : lm_alt M) : list (bv 8) :=
    lm_cont M s l a ++ (if lm_panic M a then pro_of (pro_from 1 ps) else []).

  Lemma lm_cont_at_0 ps cs s bs :
    lm_cont_at ps cs s bs 0 = lm_cont_all ps s (lm_of M (bs !!! 0)) (lm_at cs 0).
  Proof using. reflexivity. Qed.

  Lemma lm_cont_at_bs0 ps cs s bs bs' :
    bs !!! 0 = bs' !!! 0 -> lm_cont_at ps cs s bs 0 = lm_cont_at ps cs s bs' 0.
  Proof using. intro H. rewrite /lm_cont_at H. reflexivity. Qed.

  Lemma lm_cont_all_out ps s l a :
    lm_panic M a = false -> lm_cont_all ps s l a = lm_cont M s l a.
  Proof using. intro H. rewrite /lm_cont_all H. by rewrite app_nil_r. Qed.

  (* the range condition and the discipline, read at one round *)
  Lemma lm_alts_ok_at s I cs i :
    lm_alts_ok s I cs -> i < nlines I ->
    lm_ok M (lm_upto cs s (bodies_of I) i) (lm_of M (bodies_of I !!! i)) (lm_at cs i).
  Proof using. intros [_ H] Hi. exact (H i Hi). Qed.

  Lemma lm_alts_ok_len s I cs : lm_alts_ok s I cs -> length cs = nlines I.
  Proof using. by intros [H _]. Qed.

  Lemma lm_disc_input_at I i :
    lm_disc_input I -> i < nlines I -> lm_body_ok M (bodies_of I !!! i).
  Proof using.
    intros (Hb & _ & _) Hi. rewrite /nlines in Hi.
    destruct (lookup_lt_is_Some_2 (bodies_of I) i Hi) as [b Hb'].
    rewrite (list_lookup_total_correct _ _ _ Hb').
    exact (Forall_lookup_1 _ _ _ _ Hb Hb').
  Qed.

  (* ================================================================== *)
  (*  3.  DETERMINACY: TWO WITNESSES PUT THE SAME BYTES ON THE WIRE      *)
  (*                                                                    *)
  (*  Proved once, from the byte shape ([lm_laws]).  It concludes an     *)
  (*  equality of BYTES and never of indices or of states, and it cannot *)
  (*  conclude more: at the file, [RFOpenU] and [RFOpenM] print the same *)
  (*  bytes and leave different files; at the pipeline, [echo fork | cat]*)
  (*  prints on its good run exactly what the fork panic prints.  What   *)
  (*  replaces the index is the one observation everything below runs   *)
  (*  on: every alternative's own output is a '$'-FREE RUN FOLLOWED BY   *)
  (*  THE PROMPT, or sh's panic line and the prologue init then opens.   *)
  (*  The coverage-ending arm is the one exception, and the discipline's *)
  (*  own guard (the pipeline's rule D4: coverage ends at a fork failure,*)
  (*  and the discipline's block there is not a shuffle) is what keeps   *)
  (*  it out of the comparison.                                          *)
  (* ================================================================== *)
  Section determinacy.
    Context (L : lm_laws M).

    Lemma lm_cont_all_panic ps s l a :
      lm_panic M a = true ->
      lm_cont_all ps s l a = alt_panic ++ pro_of (pro_from 1 ps).
    Proof using L.
      intro H. rewrite /lm_cont_all (lml_cont_panic L s l a H) H. reflexivity.
    Qed.

    (* the state a round starts in is well-formed, round by round *)
    Lemma lm_upto_st_ok (cs : list nat) (s : lm_st M) (bs : list (list (bv 8))) (q : nat) :
      lm_st_ok M s ->
      (forall i, i < q -> lm_line_ok M (lm_of M (bs !!! i))) ->
      (forall i, i < q -> lm_ok M (lm_upto cs s bs i) (lm_of M (bs !!! i)) (lm_at cs i)) ->
      lm_st_ok M (lm_upto cs s bs q).
    Proof using L.
      intros Hs. induction q as [| q IH]; intros Hl Hok; [exact Hs |].
      cbn [lm_upto]. apply (lml_st_step L).
      - apply IH; intros i Hi; [apply Hl | apply Hok]; lia.
      - apply Hl. lia.
      - apply Hok. lia.
    Qed.

    (* THE BLOCK STEP.  Two continuations below one wire are the SAME
       BYTES, and the unprimed round is settled.  Four cases, by which
       side panicked; three of them are one lemma each and the fourth is
       [EchoDisc]'s prologue prefix-freeness. *)
    Lemma lm_cont_pair_det (ps ps' : list nat) (s s' : lm_st M) (l : lm_line M)
        (a a' : lm_alt M) (X X' : list (bv 8)) :
      Forall (fun x => x < length pro_alts) ps ->
      Forall (fun x => x < length pro_alts) ps' ->
      lm_line_ok M l -> lm_st_ok M s -> lm_st_ok M s' ->
      lm_ok M s l a -> lm_ok M s' l a' ->
      (lm_panic M a' = true -> 1 < pro_rounds ps') ->
      (lm_panic M a = true -> X <> [] -> 1 < pro_rounds ps) ->
      (lm_term M a = true -> X = []) ->
      ((exists c, lm_ok M s' l c /\ lm_term M c = true) ->
         ~ lm_merge M l (lm_cont M s' l a')) ->
      (lm_cont_all ps' s' l a' ++ X') `prefix_of` (lm_cont_all ps s l a ++ X) ->
      (lm_panic M a = true -> 1 < pro_rounds ps)
      /\ lm_cont_all ps' s' l a' = lm_cont_all ps s l a
      /\ X' `prefix_of` X.
    Proof using L.
      intros Hps Hps' Hl Hs Hs' Ha Ha' Hset' Hset Hd4 Hnm Hp.
      (* NEITHER SIDE IS THE COVERAGE-ENDING ROUND, and the two premises
         are exactly what says so.  The primed side is refuted outright;
         the unprimed side is refuted because its block would then be
         mergeable with nothing after it (D4), so the primed block sits
         INSIDE it -- and a prefix of a mergeable output is one. *)
      assert (Hfa' : lm_term M a' = false).
      { destruct (lm_term M a') eqn:Hf; [exfalso | reflexivity].
        exact (Hnm (ex_intro _ a' (conj Ha' Hf))
                   (lml_term_merge L s' l a' Hs' Ha' Hf)). }
      assert (Hfa : lm_term M a = false).
      { destruct (lm_term M a) eqn:Hf; [exfalso | reflexivity].
        rewrite (Hd4 eq_refl) app_nil_r in Hp.
        apply (Hnm (lml_term_st L s l a Ha Hf s')).
        apply (lml_merge_prefix L l _ (lm_cont_all ps s l a)).
        - etrans; [| etrans; [apply prefix_app_r; reflexivity | exact Hp]].
          rewrite /lm_cont_all. apply prefix_app_r. reflexivity.
        - rewrite /lm_cont_all (lml_term_nopanic L a Hf) app_nil_r.
          exact (lml_term_merge L s l a Hs Ha Hf). }
      destruct (lm_panic M a) eqn:Hpa; destruct (lm_panic M a') eqn:Hpa'.
      - (* BOTH PANICKED: two prologues below one wire *)
        rewrite (lm_cont_all_panic ps s l a Hpa) (lm_cont_all_panic ps' s' l a' Hpa')
          in Hp |- *.
        rewrite -(app_assoc alt_panic (pro_of (pro_from 1 ps')) X')
                -(app_assoc alt_panic (pro_of (pro_from 1 ps)) X) in Hp.
        apply wl_prefix_app_cancel in Hp.
        assert (Hd' : pro_done (pro_from 1 ps'))
          by (apply pro_from_done, Hset', eq_refl).
        pose proof (pro_from_Forall _ 1 ps Hps) as HFA.
        pose proof (pro_from_Forall _ 1 ps' Hps') as HFB.
        assert (Hcmp : pro_of (pro_from 1 ps') `prefix_of` pro_of (pro_from 1 ps)).
        { destruct (decide (X = [])) as [HX0 | HXne].
          - rewrite HX0 app_nil_r in Hp.
            etrans; [apply prefix_app_r; reflexivity | exact Hp].
          - assert (HdA : pro_done (pro_from 1 ps))
              by (apply pro_from_done, Hset; [exact eq_refl | exact HXne]).
            destruct (prefix_weak_total (pro_of (pro_from 1 ps'))
                        (pro_of (pro_from 1 ps))
                        (pro_of (pro_from 1 ps) ++ X)
                        ltac:(etrans; [apply prefix_app_r; reflexivity | exact Hp])
                        ltac:(apply prefix_app_r; reflexivity)) as [H | H];
              [exact H |].
            destruct (pro_of_prefix_free (pro_from 1 ps') (pro_from 1 ps)
                        HFB HFA HdA H) as [_ Heqp]. by rewrite Heqp. }
        destruct (pro_of_prefix_free (pro_from 1 ps) (pro_from 1 ps')
                    HFA HFB Hd' Hcmp) as [HdA Heqp].
        rewrite Heqp in Hp. apply wl_prefix_app_cancel in Hp.
        split; [intros _; by apply pro_from_done |].
        split; [by rewrite Heqp | exact Hp].
      - (* THE UNPRIMED SIDE PANICKED; the primed side printed a prompt *)
        rewrite (lm_cont_all_panic ps s l a Hpa) (lm_cont_all_out ps' s' l a' Hpa')
          in Hp |- *.
        destruct (lml_cont_shape L s' l a' Hs' Hl Ha' Hpa' Hfa') as (u & Hu & Hnd & Hvp).
        rewrite Hu in Hp |- *.
        rewrite -(app_assoc u u_prompt X')
                -(app_assoc alt_panic (pro_of (pro_from 1 ps)) X) in Hp.
        assert (Hueq : u = alt_panic).
        { apply (Hvp X' (pro_from 1 ps) X (pro_from_Forall _ 1 ps Hps)).
          left. split; [| exact Hp].
          destruct (decide (X = [])) as [HX0 | HXne]; [by left | right].
          apply pro_from_done, Hset; [exact eq_refl | exact HXne]. }
        rewrite Hueq in Hp |- *. apply wl_prefix_app_cancel in Hp.
        assert (HdA : pro_done (pro_from 1 ps)).
        { destruct (decide (X = [])) as [HX0 | HXne];
            [| apply pro_from_done, Hset; [exact eq_refl | exact HXne]].
          rewrite HX0 app_nil_r in Hp.
          destruct (decide (pro_done (pro_from 1 ps))) as [Hy | Hopen];
            [exact Hy | exfalso].
          assert (H1 : (u_prompt ++ X') !! 0 = Some (Z_to_bv 8 36%Z))
            by (rewrite lookup_app_l; [exact u_prompt_head | exact u_prompt_pos]).
          assert (H2 : pro_of (pro_from 1 ps) !! 0 = Some (Z_to_bv 8 36%Z))
            by (eapply lb_prefix_lookup; [exact Hp | exact H1]).
          pose proof (pro_of_open_head (pro_from 1 ps) _ Hopen H2) as Hv.
          rewrite (_ : bv_unsigned (Z_to_bv 8 36%Z) = 36%Z) in Hv;
            [lia | by vm_compute]. }
        assert (Heqp : pro_of (pro_from 1 ps) = u_prompt)
          by (apply (lb_prompt_of_dollar (pro_from 1 ps) X X');
              [exact (pro_from_Forall _ 1 ps Hps) | exact HdA | exact Hp]).
        rewrite Heqp in Hp. apply wl_prefix_app_cancel in Hp.
        split; [intros _; by apply pro_from_done |].
        split; [by rewrite Heqp | exact Hp].
      - (* THE PRIMED SIDE PANICKED; the unprimed printed a prompt *)
        rewrite (lm_cont_all_out ps s l a Hpa) (lm_cont_all_panic ps' s' l a' Hpa')
          in Hp |- *.
        destruct (lml_cont_shape L s l a Hs Hl Ha Hpa Hfa) as (u & Hu & Hnd & Hvp).
        rewrite Hu in Hp |- *.
        rewrite -(app_assoc alt_panic (pro_of (pro_from 1 ps')) X')
                -(app_assoc u u_prompt X) in Hp.
        assert (Hd' : pro_done (pro_from 1 ps'))
          by (apply pro_from_done, Hset', eq_refl).
        assert (Hueq : u = alt_panic)
          by (apply (Hvp X (pro_from 1 ps') X' (pro_from_Forall _ 1 ps' Hps'));
              right; split; [exact Hd' | exact Hp]).
        rewrite Hueq in Hp |- *. apply wl_prefix_app_cancel in Hp.
        assert (Heqp : pro_of (pro_from 1 ps') = u_prompt)
          by (apply (lb_prompt_of_dollar_r (pro_from 1 ps') X' X);
              [exact (pro_from_Forall _ 1 ps' Hps') | exact Hd' | exact Hp]).
        rewrite Heqp in Hp. apply wl_prefix_app_cancel in Hp.
        split; [intros Hq; discriminate |].
        split; [by rewrite Heqp | exact Hp].
      - (* NEITHER PANICKED: the '$'-split settles it, whatever they were *)
        rewrite (lm_cont_all_out ps s l a Hpa) (lm_cont_all_out ps' s' l a' Hpa')
          in Hp |- *.
        destruct (lml_cont_shape L s l a Hs Hl Ha Hpa Hfa) as (u & Hu & Hnd & _).
        destruct (lml_cont_shape L s' l a' Hs' Hl Ha' Hpa' Hfa') as (u' & Hu' & Hnd' & _).
        rewrite Hu Hu' in Hp |- *.
        rewrite -(app_assoc u' u_prompt X') -(app_assoc u u_prompt X) in Hp.
        destruct (lb_dollar_split u u' X X' Hnd Hnd' Hp) as [-> HX].
        split; [intros Hq; discriminate |].
        split; [reflexivity | exact HX].
    Qed.

    (* THE SEQUENCE STEP.  Two block sequences below one wire have the
       same BODIES and the same BYTES, round by round -- and nothing is
       concluded about the two states, which may genuinely differ and go
       on differing while the wire stays the same. *)
    Lemma lm_seq_prefix_det (q' : nat) :
      forall (ps ps' cs cs' : list nat) (s s' : lm_st M)
             (bs bs' : list (list (bv 8))) (q : nat) (t' t : list (bv 8)),
        Forall (fun a => a < length pro_alts) ps ->
        Forall (fun a => a < length pro_alts) ps' ->
        lm_pro_idx cs' q' < pro_rounds ps' ->
        0 < pro_rounds ps ->
        (forall i, i < q -> lm_pro_idx cs i < pro_rounds ps) ->
        (t <> [] -> lm_pro_idx cs q < pro_rounds ps) ->
        q' <= length bs' -> q <= length bs ->
        lm_st_ok M s -> lm_st_ok M s' ->
        (forall i, i < q -> lm_line_ok M (lm_of M (bs !!! i))) ->
        (forall i, i < q ->
           lm_ok M (lm_upto cs s bs i) (lm_of M (bs !!! i)) (lm_at cs i)) ->
        (forall i, i < q' ->
           lm_ok M (lm_upto cs' s' bs' i) (lm_of M (bs' !!! i)) (lm_at cs' i)) ->
        (forall i, i < q' -> lm_term M (lm_at cs i) = true -> S i = q /\ t = []) ->
        (forall i, i < q' ->
           (exists c, lm_ok M (lm_upto cs' s' bs' i) (lm_of M (bs' !!! i)) c
                      /\ lm_term M c = true) ->
           ~ lm_merge M (lm_of M (bs' !!! i))
               (lm_cont M (lm_upto cs' s' bs' i) (lm_of M (bs' !!! i)) (lm_at cs' i))) ->
        Forall (fun l => wl_nl ∉ l) bs -> Forall (fun l => wl_nl ∉ l) bs' ->
        wl_nl ∉ t' -> wl_nl ∉ t ->
        (lm_seq ps' cs' s' bs' q' ++ t') `prefix_of` (lm_seq ps cs s bs q ++ t) ->
        q' <= q /\ take q' bs' = take q' bs
        /\ lm_pro_idx cs q' < pro_rounds ps
        /\ lm_seq ps' cs' s' bs' q' = lm_seq ps cs s bs q'
        /\ (q' = q -> t' `prefix_of` t)
        /\ (q' < q -> t' `prefix_of` bs !!! q')
        /\ (forall i, i < q' ->
              lm_cont_at ps' cs' s' bs' i = lm_cont_at ps cs s bs i).
    Proof using L.
      induction q' as [| n IH];
        intros ps ps' cs cs' s s' bs bs' q t' t Hps Hps' Hlt' Hpos Hbelow Htlast
          Hlb' Hlb Hs Hs' Hline Hokc Hokc' Hd4u Hnmp Hnb Hnb' Hnt' Hnt Hpre.
      { rewrite lm_seq_0 app_nil_l in Hpre.
        split; [lia |]. split; [by rewrite !take_0 |].
        split; [cbn [lm_pro_idx]; lia |]. split; [reflexivity |].
        split; [| split; [| intros i Hi; lia]].
        - intros Hq. rewrite -Hq lm_seq_0 app_nil_l in Hpre. exact Hpre.
        - intros Hq. destruct q as [| p]; [lia |].
          rewrite lm_seq_cons_assoc in Hpre.
          exact (wl_prefix_nonl_of_line t' (bs !!! 0) _ Hnt' Hpre). }
      (* the primed side has a block, so the unprimed side has one *)
      destruct q as [| p].
      { exfalso. rewrite lm_seq_0 app_nil_l lm_seq_cons_assoc in Hpre.
        exact (wl_raw_line_not_prefix_nonl (bs' !!! 0) _ t Hnt Hpre). }
      rewrite !lm_seq_cons_assoc in Hpre.
      assert (Hn0' : wl_nl ∉ bs' !!! 0) by (apply lb_nonl_lta; [exact Hnb' | lia]).
      assert (Hn0 : wl_nl ∉ bs !!! 0) by (apply lb_nonl_lta; [exact Hnb | lia]).
      destruct (wl_raw_line_prefix_det _ _ _ _ Hn0' Hn0 Hpre) as [Hhd Hrest].
      rewrite (lm_cont_at_bs0 ps' cs' s' bs' bs ltac:(by rewrite Hhd)) in Hrest.
      (* the head block: one line, two alternatives, one wire *)
      assert (Hl0 : lm_line_ok M (lm_of M (bs !!! 0))) by (apply Hline; lia).
      assert (Ha0 : lm_ok M s (lm_of M (bs !!! 0)) (lm_at cs 0))
        by exact (Hokc 0 ltac:(lia)).
      assert (Ha0' : lm_ok M s' (lm_of M (bs !!! 0)) (lm_at cs' 0)).
      { rewrite -Hhd. exact (Hokc' 0 ltac:(lia)). }
      assert (Hset' : lm_panic M (lm_at cs' 0) = true -> 1 < pro_rounds ps').
      { intros H3. eapply Nat.le_lt_trans; [| exact Hlt'].
        rewrite -(lm_pro_idx_Sp cs' 0 H3). apply lm_pro_idx_mono. lia. }
      assert (Hsetu : lm_panic M (lm_at cs 0) = true ->
                (lm_seq (pro_from (lm_pro_idx cs 1) ps) (drop 1 cs)
                   (lm_upto cs s bs 1) (drop 1 bs) p ++ t) <> [] ->
                1 < pro_rounds ps).
      { intros H3 Hne. destruct p as [| p0].
        - assert (Htne : t <> []).
          { intro Hq. apply Hne. by rewrite lm_seq_0 app_nil_l Hq. }
          pose proof (Htlast Htne) as Hb1.
          rewrite (lm_pro_idx_Sp cs 0 H3) in Hb1. cbn [lm_pro_idx] in Hb1. lia.
        - pose proof (Hbelow 1 ltac:(lia)) as Hb1.
          rewrite (lm_pro_idx_Sp cs 0 H3) in Hb1. cbn [lm_pro_idx] in Hb1. lia. }
      (* D4 AT THE HEAD ROUND, the two sides: if the unprimed head round
         ends coverage it is the LAST block and the tail is empty; and
         the primed head block is not mergeable *)
      assert (Hd4h : lm_term M (lm_at cs 0) = true ->
                (lm_seq (pro_from (lm_pro_idx cs 1) ps) (drop 1 cs)
                   (lm_upto cs s bs 1) (drop 1 bs) p ++ t) = []).
      { intros Hf. destruct (Hd4u 0 ltac:(lia) Hf) as [Hq Ht].
        assert (Hp0 : p = 0) by lia.
        by rewrite Hp0 lm_seq_0 Ht. }
      assert (Hnmh : (exists c, lm_ok M s' (lm_of M (bs !!! 0)) c /\ lm_term M c = true) ->
                ~ lm_merge M (lm_of M (bs !!! 0))
                    (lm_cont M s' (lm_of M (bs !!! 0)) (lm_at cs' 0))).
      { rewrite -Hhd. exact (Hnmp 0 ltac:(lia)). }
      rewrite !lm_cont_at_0 in Hrest.
      destruct (lm_cont_pair_det ps ps' s s' (lm_of M (bs !!! 0))
                  (lm_at cs 0) (lm_at cs' 0) _ _
                  Hps Hps' Hl0 Hs Hs' Ha0 Ha0' Hset' Hsetu Hd4h Hnmh Hrest)
        as (Hround1 & Hcont & Hrest2).
      assert (Hlt1 : lm_pro_idx cs 1 < pro_rounds ps).
      { destruct (lm_panic M (lm_at cs 0)) eqn:H3.
        - rewrite (lm_pro_idx_Sp cs 0 H3). cbn [lm_pro_idx]. by apply Hround1.
        - rewrite (lm_pro_idx_Sn cs 0 H3). cbn [lm_pro_idx]. lia. }
      (* the states after the head block, which may already differ *)
      assert (Hs1 : lm_st_ok M (lm_upto cs s bs 1))
        by (cbn [lm_upto]; exact (lml_st_step L s _ _ Hs Hl0 Ha0)).
      assert (Hs1' : lm_st_ok M (lm_upto cs' s' bs' 1)).
      { cbn [lm_upto]. rewrite Hhd. exact (lml_st_step L s' _ _ Hs' Hl0 Ha0'). }
      destruct (IH (pro_from (lm_pro_idx cs 1) ps) (pro_from (lm_pro_idx cs' 1) ps')
                  (drop 1 cs) (drop 1 cs')
                  (lm_upto cs s bs 1) (lm_upto cs' s' bs' 1)
                  (drop 1 bs) (drop 1 bs') p t' t
                  (pro_from_Forall _ _ ps Hps) (pro_from_Forall _ _ ps' Hps'))
        as (Hle & Htk & Hrd & Heq & Hteq & Htlt & Hcnt).
      { rewrite pro_rounds_from.
        pose proof (lm_pro_idx_add cs' 1 n) as Hadd.
        replace (1 + n) with (S n) in Hadd by lia. lia. }
      { rewrite pro_rounds_from. lia. }
      { intros i Hi. rewrite pro_rounds_from.
        pose proof (lm_pro_idx_add cs 1 i) as Hadd.
        replace (1 + i) with (S i) in Hadd by lia.
        pose proof (Hbelow (S i) ltac:(lia)). lia. }
      { intros Htne. rewrite pro_rounds_from.
        pose proof (lm_pro_idx_add cs 1 p) as Hadd.
        replace (1 + p) with (S p) in Hadd by lia.
        pose proof (Htlast Htne). lia. }
      { rewrite length_drop. lia. }
      { rewrite length_drop. lia. }
      { exact Hs1. }
      { exact Hs1'. }
      { intros i Hi. rewrite lb_lookup_total_drop. apply Hline. lia. }
      { intros i Hi. rewrite lm_upto_drop /lm_at !lb_lookup_total_drop. apply Hokc. lia. }
      { intros i Hi. rewrite lm_upto_drop /lm_at !lb_lookup_total_drop. apply Hokc'. lia. }
      { intros i Hi Hf. rewrite /lm_at lb_lookup_total_drop in Hf.
        replace (1 + i) with (S i) in Hf by lia.
        destruct (Hd4u (S i) ltac:(lia) Hf) as [Hq Ht].
        split; [lia | exact Ht]. }
      { intros i Hi. rewrite /lm_at !lb_lookup_total_drop lm_upto_drop.
        replace (1 + i) with (S i) by lia. apply Hnmp. lia. }
      { by apply lb_Forall_drop. }
      { by apply lb_Forall_drop. }
      { exact Hnt'. }
      { exact Hnt. }
      { exact Hrest2. }
      assert (Hlbn : S n <= length bs) by lia.
      split; [lia |].
      split; [by rewrite (lb_take_S n bs' Hlb') (lb_take_S n bs Hlbn) Hhd Htk |].
      split.
      { pose proof (lm_pro_idx_add cs 1 n) as Hadd.
        replace (1 + n) with (S n) in Hadd by lia.
        rewrite pro_rounds_from in Hrd. lia. }
      split.
      { rewrite (lm_seq_cons ps' cs' s' bs' n) (lm_seq_cons ps cs s bs n).
        rewrite Heq /lm_blk Hhd.
        rewrite (lm_cont_at_bs0 ps' cs' s' bs' bs ltac:(by rewrite Hhd)).
        by rewrite !lm_cont_at_0 Hcont. }
      split.
      { intros Hqe. apply Hteq. lia. }
      split.
      { intros Hqlt.
        pose proof (Htlt ltac:(lia)) as H.
        rewrite lb_lookup_total_drop in H.
        replace (1 + n) with (S n) in H by lia. exact H. }
      (* ...and the blocks themselves, round by round *)
      intros i Hi. destruct i as [| j].
      { rewrite (lm_cont_at_bs0 ps' cs' s' bs' bs ltac:(by rewrite Hhd)).
        rewrite !lm_cont_at_0. exact Hcont. }
      pose proof (Hcnt j ltac:(lia)) as H.
      rewrite !lm_cont_at_drop in H.
      by replace (1 + j) with (S j) in H by lia.
    Qed.

    (* ...AND THE SESSION TRANSCRIPTS THEMSELVES, at two boot states.
       This is what the stage spends: two resolutions below one wire are
       the same bytes, and the discipline's input is a prefix of the
       claim's. *)
    Lemma lm_sess_prefix_det (ps ps' cs cs' : list nat) (s s' : lm_st M)
        (I' I : list (bv 8)) :
      Forall (fun a => a < length pro_alts) ps ->
      lm_pro_ok ps' cs' (nlines I') ->
      lm_alts_ok s I cs -> lm_alts_ok s' I' cs' ->
      lm_pro_pin ps cs I -> lm_disc_input I -> lm_disc_input I' ->
      lm_st_ok M s -> lm_st_ok M s' ->
      (forall i, i < nlines I' -> lm_term M (lm_at cs i) = true ->
         S i = nlines I /\ rest_of I = []) ->
      (forall i, i < nlines I' ->
         (exists c, lm_ok M (lm_upto cs' s' (bodies_of I') i) (lm_of M (bodies_of I' !!! i)) c
                    /\ lm_term M c = true) ->
         ~ lm_merge M (lm_of M (bodies_of I' !!! i))
             (lm_cont M (lm_upto cs' s' (bodies_of I') i)
                (lm_of M (bodies_of I' !!! i)) (lm_at cs' i))) ->
      lm_sess ps' cs' s' I' `prefix_of` lm_sess ps cs s I ->
      I' `prefix_of` I /\ lm_pro_ok ps cs (nlines I')
      /\ lm_sess ps' cs' s' I' = lm_sess ps cs s I'
      /\ (forall i, i < nlines I' ->
            lm_cont_at ps' cs' s' (bodies_of I') i = lm_cont_at ps cs s (bodies_of I) i).
    Proof using L.
      intros Hps [Hps' Hlt'] Hcs Hcs' Hpin Hd Hd' Hs Hs' Hd4 Hnm Hpre.
      assert (Hdone' : pro_done ps') by (apply pro_done_rounds; lia).
      (* the PROLOGUES: below one wire, and the primed one is settled *)
      assert (Hpre0 : pro_of ps' `prefix_of` pro_of ps).
      { destruct (decide (I = [])) as [HI0 | HI].
        - rewrite HI0 lm_sess_nil in Hpre. etrans; [| exact Hpre].
          rewrite /lm_sess. by apply prefix_app_r.
        - assert (HdA : pro_done ps).
          { apply pro_done_rounds.
            pose proof (Hpin 0 (nstarted_pos I HI)) as H0.
            cbn [lm_pro_idx] in H0. lia. }
          assert (H1 : pro_of ps' `prefix_of` lm_sess ps cs s I).
          { etrans; [| exact Hpre]. rewrite /lm_sess. by apply prefix_app_r. }
          assert (H2 : pro_of ps `prefix_of` lm_sess ps cs s I)
            by (rewrite /lm_sess; by apply prefix_app_r).
          destruct (prefix_weak_total _ _ _ H1 H2) as [H | H]; [exact H |].
          destruct (pro_of_prefix_free ps' ps Hps' Hps HdA H) as [_ Heq].
          by rewrite Heq. }
      destruct (pro_of_prefix_free ps ps' Hps Hps' Hdone' Hpre0) as [Hdps Heq0].
      assert (Hpos : 0 < pro_rounds ps) by (by apply pro_done_rounds).
      rewrite /lm_sess Heq0 in Hpre. apply wl_prefix_app_cancel in Hpre.
      assert (Hbelow : forall i, i < nlines I -> lm_pro_idx cs i < pro_rounds ps).
      { intros i Hi. apply Hpin. pose proof (nlines_le_nstarted I). lia. }
      assert (Htlast : rest_of I <> [] -> lm_pro_idx cs (nlines I) < pro_rounds ps).
      { intros Hne. apply Hpin. rewrite /nstarted.
        case_decide as Hz; [by destruct (Hne Hz) | lia]. }
      assert (Hlb' : nlines I' <= length (bodies_of I')) by (rewrite /nlines; lia).
      assert (Hlb : nlines I <= length (bodies_of I)) by (rewrite /nlines; lia).
      assert (Hline : forall i, i < nlines I -> lm_line_ok M (lm_of M (bodies_of I !!! i)))
        by (intros i Hi; exact (lml_body_line L _ (lm_disc_input_at I i Hd Hi))).
      assert (Hokc : forall i, i < nlines I ->
                lm_ok M (lm_upto cs s (bodies_of I) i) (lm_of M (bodies_of I !!! i))
                  (lm_at cs i))
        by (intros i Hi; exact (lm_alts_ok_at s I cs i Hcs Hi)).
      assert (Hokc' : forall i, i < nlines I' ->
                lm_ok M (lm_upto cs' s' (bodies_of I') i)
                  (lm_of M (bodies_of I' !!! i)) (lm_at cs' i))
        by (intros i Hi; exact (lm_alts_ok_at s' I' cs' i Hcs' Hi)).
      destruct (lm_seq_prefix_det (nlines I') ps ps' cs cs' s s'
                  (bodies_of I) (bodies_of I') (nlines I) (rest_of I') (rest_of I)
                  Hps Hps' Hlt' Hpos Hbelow Htlast Hlb' Hlb Hs Hs'
                  Hline Hokc Hokc' Hd4 Hnm
                  (wl_cut_bodies_nonl I) (wl_cut_bodies_nonl I')
                  (wl_cut_rest_nonl I') (wl_cut_rest_nonl I) Hpre)
        as (Hqle & Htk & Hround & Hseq & Hteq & Htlt & Hcnt).
      assert (HI' : I' `prefix_of` I).
      { apply wl_cut_prefix_of.
        - assert (Hb' : bodies_of I' = take (nlines I') (bodies_of I))
            by (rewrite -Htk take_ge; [reflexivity | rewrite /nlines; lia]).
          rewrite Hb'. apply prefix_take.
        - exact Hteq.
        - exact Htlt. }
      split; [exact HI' |]. split; [split; [exact Hps | exact Hround] |].
      split; [| exact Hcnt].
      rewrite /lm_sess Heq0. do 2 f_equal. rewrite Hseq.
      apply lm_seq_bs_ext. intros j Hj. symmetry.
      exact (lb_lta_take_eq (bodies_of I) (bodies_of I') (nlines I') j Htk Hj).
    Qed.
  End determinacy.

  Lemma lm_pro_pin_of_ok ps cs I :
    lm_pro_ok ps cs (nlines I) -> lm_pro_pin ps cs I.
  Proof using.
    intros [_ Hlt] q Hq. rewrite /nstarted in Hq.
    (* the pointer is monotone in the index *)
    assert (Hmono : forall i j, i <= j -> lm_pro_idx cs i <= lm_pro_idx cs j).
    { intros i j Hij. induction Hij as [| j Hij IH]; [lia |].
      cbn [lm_pro_idx]. destruct (lm_panic M (lm_at cs j)); lia. }
    case_decide as Hr.
    - pose proof (Hmono q (nlines I) ltac:(lia)). lia.
    - destruct (decide (q < nlines I)) as [Hlt' | Hge].
      + pose proof (Hmono q (nlines I) ltac:(lia)). lia.
      + assert (q = nlines I) as -> by lia. exact Hlt.
  Qed.


  (* ---- THE SESSION'S SNOC LAWS (the file's [sessf_snoc_nl] and its
          three companions, once) ---- *)
  Lemma lm_seq_bs_app ps cs s bs bs' q :
    q <= length bs -> lm_seq ps cs s (bs ++ bs') q = lm_seq ps cs s bs q.
  Proof using.
    intro Hq. apply lm_seq_bs_ext. intros j Hj.
    rewrite !list_lookup_total_alt lookup_app_l; [reflexivity | lia].
  Qed.

  Lemma lm_sess_snoc_nl ps cs s I :
    lm_sess ps cs s (I ++ [wl_nl])
    = lm_sess ps cs s I
      ++ wl_nl :: lm_cont_at ps cs s (bodies_of I ++ [rest_of I]) (nlines I).
  Proof using.
    assert (Hidx : (bodies_of I ++ [rest_of I]) !!! (nlines I) = rest_of I).
    { rewrite list_lookup_total_alt
        (lookup_app_r (bodies_of I) [rest_of I] (nlines I)
           ltac:(rewrite /nlines; lia)).
      rewrite /nlines Nat.sub_diag. reflexivity. }
    rewrite {1}/lm_sess bodies_of_snoc_nl nlines_snoc_nl rest_of_snoc_nl.
    rewrite lm_seq_S (lm_seq_bs_app ps cs s (bodies_of I) [rest_of I]
                        (nlines I) ltac:(rewrite /nlines; lia)).
    rewrite /lm_blk Hidx app_nil_r /lm_sess.
    by rewrite !app_assoc.
  Qed.

  Lemma lm_sess_snoc_other ps cs s I b :
    b <> wl_nl -> lm_sess ps cs s (I ++ [b]) = lm_sess ps cs s I ++ [b].
  Proof using.
    intro Hb. rewrite /lm_sess (bodies_of_snoc_other I b Hb)
      (nlines_snoc_other I b Hb) (rest_of_snoc_other I b Hb).
    by rewrite !app_assoc.
  Qed.

  Lemma lm_sess_step ps cs s I b :
    lm_sess ps cs s I `prefix_of` lm_sess ps cs s (I ++ [b]).
  Proof using.
    destruct (decide (b = wl_nl)) as [-> | Hb].
    - rewrite lm_sess_snoc_nl. by eexists.
    - rewrite (lm_sess_snoc_other ps cs s I b Hb). by eexists.
  Qed.

  Lemma lm_sess_mono ps cs s I I' :
    I `prefix_of` I' -> lm_sess ps cs s I `prefix_of` lm_sess ps cs s I'.
  Proof using.
    intros [k ->]. induction k as [| b k IH] using rev_ind.
    - rewrite app_nil_r. reflexivity.
    - rewrite app_assoc. etrans; [exact IH | apply lm_sess_step].
  Qed.

  (* ---- THE CHOICE LIST IS READ ONLY BELOW THE INPUT'S LINE COUNT: two
     lists that agree there give the same pointer, states and transcript
     ([FileDisc.alt_seq_f_cs_ext]'s shape, once) ---- *)
  Lemma lm_pro_idx_ext cs1 cs2 q :
    (forall j, j < q -> cs1 !!! j = cs2 !!! j) ->
    forall j, j <= q -> lm_pro_idx cs1 j = lm_pro_idx cs2 j.
  Proof using.
    intros H j. induction j as [| j IH]; intros Hj; [reflexivity |].
    cbn [lm_pro_idx]. rewrite IH; [| lia]. by rewrite /lm_at (H j ltac:(lia)).
  Qed.

  Lemma lm_upto_cs_ext cs1 cs2 s bs q :
    (forall j, j < q -> cs1 !!! j = cs2 !!! j) ->
    lm_upto cs1 s bs q = lm_upto cs2 s bs q.
  Proof using.
    intros H. induction q as [| q IH]; [reflexivity |].
    cbn [lm_upto]. rewrite IH; [| intros j Hj; apply H; lia].
    by rewrite /lm_at (H q ltac:(lia)).
  Qed.

  Lemma lm_seq_cs_ext ps cs1 cs2 s bs q :
    (forall j, j < q -> cs1 !!! j = cs2 !!! j) ->
    lm_seq ps cs1 s bs q = lm_seq ps cs2 s bs q.
  Proof using.
    intros H. rewrite /lm_seq. f_equal. apply list_fmap_ext.
    intros i x Hx. apply lookup_seq in Hx as [-> Hi].
    rewrite /lm_blk /lm_cont_at /lm_at.
    rewrite (lm_upto_cs_ext cs1 cs2 s bs (0 + i)
               ltac:(intros j Hj; apply H; lia)).
    rewrite (H (0 + i) ltac:(lia)).
    rewrite (lm_pro_idx_ext cs1 cs2 q H (0 + i) ltac:(lia)). reflexivity.
  Qed.

  Lemma lm_sess_cs_ext ps cs1 cs2 s I :
    (forall j, j < nlines I -> cs1 !!! j = cs2 !!! j) ->
    lm_sess ps cs1 s I = lm_sess ps cs2 s I.
  Proof using.
    intros H. rewrite /lm_sess. by rewrite (lm_seq_cs_ext ps cs1 cs2 s _ _ H).
  Qed.

  (* ---- THE RANGE CONDITION'S OWN LAWS ---- *)
  Lemma lm_alts_ok_nil s I : nlines I = 0 -> lm_alts_ok s I [].
  Proof using. intros Hn. split; [by rewrite Hn | intros i Hi; lia]. Qed.

  (* a prefix of the input is checked by the prefix of the list *)
  Lemma lm_alts_ok_prefix s I I' cs :
    I `prefix_of` I' -> lm_alts_ok s I' cs -> lm_alts_ok s I (take (nlines I) cs).
  Proof using.
    intros Hp [Hlen H].
    destruct (bodies_of_prefix I I' Hp) as [z Hz].
    assert (Hle : nlines I <= nlines I') by (apply nlines_prefix; exact Hp).
    assert (Hbod : forall j, j < nlines I -> bodies_of I' !!! j = bodies_of I !!! j).
    { intros j Hj. rewrite Hz !list_lookup_total_alt lookup_app_l;
        [reflexivity | rewrite /nlines in Hj; lia]. }
    assert (Htk : forall j, j < nlines I -> take (nlines I) cs !!! j = cs !!! j).
    { intros j Hj. rewrite !list_lookup_total_alt lookup_take; [done | lia]. }
    split; [rewrite length_take; lia |].
    intros i Hi.
    rewrite /lm_at (Htk i Hi) -(Hbod i Hi).
    rewrite (lm_upto_cs_ext (take (nlines I) cs) cs s (bodies_of I) i
               ltac:(intros j Hj; apply Htk; lia)).
    rewrite (lm_upto_bs_ext cs s (bodies_of I) (bodies_of I') i
               ltac:(intros j Hj; symmetry; apply Hbod; lia)).
    exact (H i ltac:(lia)).
  Qed.

  (* AT A STATE-FREE RANGE CONDITION the list is checked entry by entry,
     at any one state ([Forall2], the landed instances' reading) *)
  Lemma lm_alts_ok_nostate s I cs :
    (forall s1 s2 l a, lm_ok M s1 l a -> lm_ok M s2 l a) ->
    lm_alts_ok s I cs
    <-> Forall2 (fun l c => lm_ok M s l (lm_dec M c)) (lm_of M <$> bodies_of I) cs.
  Proof using.
    intros Hst. split.
    - intros [Hlen H]. apply Forall2_same_length_lookup_2.
      { rewrite length_fmap Hlen. reflexivity. }
      intros i l c Hl Hc.
      rewrite list_lookup_fmap in Hl.
      destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
      cbn in Hl. injection Hl as <-.
      assert (Hi : i < nlines I) by (rewrite /nlines; by eapply lookup_lt_Some).
      pose proof (H i Hi) as Hok.
      rewrite /lm_at (list_lookup_total_correct _ _ _ Hc)
              (list_lookup_total_correct _ _ _ Hb) in Hok.
      exact (Hst _ _ _ _ Hok).
    - intros HF. pose proof (Forall2_length _ _ _ HF) as Hl.
      rewrite length_fmap in Hl.
      split; [rewrite /nlines; lia |].
      intros i Hi. rewrite /nlines in Hi.
      destruct (lookup_lt_is_Some_2 (bodies_of I) i Hi) as [b Hb].
      assert (Hl' : (lm_of M <$> bodies_of I) !! i = Some (lm_of M b))
        by (rewrite list_lookup_fmap Hb; reflexivity).
      destruct (Forall2_lookup_l _ _ _ _ _ HF Hl') as (c & Hc & Hok).
      rewrite /lm_at (list_lookup_total_correct cs i c Hc)
              (list_lookup_total_correct _ _ _ Hb).
      exact (Hst _ _ _ _ Hok).
  Qed.

  (* ====================================================================== *)
  (*  THE DISCIPLINE AND THE CLAIM, ONCE                                     *)
  (*                                                                        *)
  (*  [EchoDisc.disc_pt]/[disc_seg']/[disc]/[expected_rel]/[good_out] with   *)
  (*  the era's boot state a parameter ([tt] where no line touches the file  *)
  (*  system).  The per-point rule is the RELAXED per-line one at all three  *)
  (*  applications (ruled 2026-09-23): what the wire must show at every      *)
  (*  input byte is the transcript of the COMPLETE lines typed so far.       *)
  (* ====================================================================== *)

  Definition lm_disc_pt (ps cs : list nat) (s : lm_st M) (p : list mobs) : Prop :=
    lm_sess ps cs s (done_of (ins p)) `prefix_of` obs_wire Uart0 p.

  (* D4, [PipeDisc.d4_p] at the determinacy section's guard: a round whose
     line admits a coverage-ending arm at the round's state and whose
     continuation is a mergeable
     output is the input's LAST line, and the input ends at its newline --
     the discipline reads nothing of the era past such an arm.  Vacuous
     where no arm ends coverage. *)
  Definition lm_d4 (cs : list nat) (s : lm_st M) (I : list (bv 8)) : Prop :=
    forall i, i < nlines I ->
      (exists c, lm_ok M (lm_upto cs s (bodies_of I) i) (lm_of M (bodies_of I !!! i)) c
                 /\ lm_term M c = true) ->
      lm_merge M (lm_of M (bodies_of I !!! i))
        (lm_cont M (lm_upto cs s (bodies_of I) i) (lm_of M (bodies_of I !!! i)) (lm_at cs i)) ->
      nlines I = S i /\ rest_of I = [].

  Lemma lm_d4_noterm cs s I :
    (forall a, lm_term M a = false) -> lm_d4 cs s I.
  Proof using.
    intros Hnt i _ (c & _ & Hc). rewrite Hnt in Hc. discriminate Hc.
  Qed.

  (* THE PER-CYCLE DISCIPLINE: D3, the range condition, D4, and at every
     input byte D1 under ONE resolution of the prologue's and the per-line
     alternatives, read at the era's boot state *)
  Definition lm_disc_seg' (s : lm_st M) (seg : list mobs) : Prop :=
    lm_disc_input (ins seg)
    /\ exists ps cs : list nat,
         lm_alts_ok s (ins seg) cs
         /\ lm_d4 cs s (ins seg)
         /\ forall p : list mobs, p ∈ in_pres seg ->
              lm_pro_ok ps cs (nlines (ins p)) /\ lm_disc_pt ps cs s p.

  (* ...and at the whole history: every power cycle is disciplined at SOME
     admissible boot state *)
  Definition lm_disc (h : list mobs) : Prop :=
    Forall (fun seg => exists s, lm_st_ok M s /\ lm_disc_seg' s seg) (cycles_of h).

  (* THE OUTPUT CLAIM for one power cycle, at a boot state: everything on the
     console wire is a prefix of the transcript this cycle's input calls for,
     under some resolution *)
  Definition lm_expected_rel (s : lm_st M) (I out : list (bv 8)) : Prop :=
    exists ps cs : list nat,
      lm_pro_ok ps cs (nlines I)
      /\ lm_alts_ok s I cs
      /\ out `prefix_of` lm_sess ps cs s I.

  Lemma lm_expected_rel_out_mono s I out out' :
    out' `prefix_of` out -> lm_expected_rel s I out -> lm_expected_rel s I out'.
  Proof using.
    intros Hp (ps & cs & Hok & Hcs & Hout). exists ps, cs.
    split; [exact Hok |]. split; [exact Hcs |]. by etrans.
  Qed.

  Definition lm_good_out (s : lm_st M) (seg : list mobs) : Prop :=
    lm_expected_rel s (ins seg) (obs_wire Uart0 seg).

  (* ---- THE INPUT DISCIPLINE'S CLOSURE LAWS, at the byte laws ---- *)
  Section byte_laws.
    Context (B : lm_byte_laws M).

    Lemma lm_disc_input_snoc I b : lm_disc_input (I ++ [b]) -> lm_disc_input I.
    Proof using B.
      intros (Hb & Hr & Hs). destruct (decide (b = wl_nl)) as [-> | Hne].
      - rewrite bodies_of_snoc_nl in Hb.
        apply Forall_app in Hb as [Hb1 Hb2]. rewrite Forall_singleton in Hb2.
        split; [exact Hb1 |]. split; [exact (lmb_body_bytes B _ Hb2) |].
        exact (lmb_body_short B _ Hb2).
      - rewrite (bodies_of_snoc_other I b Hne) in Hb.
        rewrite (rest_of_snoc_other I b Hne) in Hr, Hs.
        apply Forall_app in Hr as [Hr1 _].
        split; [exact Hb |]. split; [exact Hr1 |].
        rewrite (length_app (rest_of I) [b]) in Hs. cbn [length] in Hs. lia.
    Qed.

    Lemma lm_disc_input_prefix I I' :
      I `prefix_of` I' -> lm_disc_input I' -> lm_disc_input I.
    Proof using B.
      intros [k ->]. induction k as [| b k IH] using rev_ind; intro Hd.
      - by rewrite app_nil_r in Hd.
      - apply IH. rewrite app_assoc in Hd. exact (lm_disc_input_snoc _ _ Hd).
    Qed.

    Lemma lm_disc_input_body I i l :
      lm_disc_input I -> bodies_of I !! i = Some l -> lm_body_ok M l.
    Proof using. intros (Hb & _ & _) Hi. exact (Forall_lookup_1 _ _ _ _ Hb Hi). Qed.

    Lemma lm_disc_input_byte I b :
      lm_disc_input I -> b ∈ I -> lm_body_byte M b \/ b = wl_nl.
    Proof using B.
      intros Hd Hin. pose proof Hd as (Hb & Hr & _).
      rewrite (wl_cut_join I) in Hin.
      apply elem_of_app in Hin as [Hin | Hin].
      - destruct (join_elem_of (bodies_of I) b Hin) as [-> | (l & Hl & Hbl)];
          [by right | left].
        apply elem_of_list_lookup in Hl as [k Hk].
        pose proof (lmb_body_bytes B l (lm_disc_input_body I k l Hd Hk)) as Hfb.
        exact (proj1 (Forall_forall _ _) Hfb b Hbl).
      - left. exact (proj1 (Forall_forall _ _) Hr b Hin).
    Qed.

    (* a disciplined byte is the newline or printable: what every refutation
       of a control byte reads *)
    Lemma lm_disc_input_byte_val I b :
      lm_disc_input I -> b ∈ I ->
      bv_unsigned b = 10%Z \/ (32 <= bv_unsigned b < 127)%Z.
    Proof using B.
      intros Hd Hin. destruct (lm_disc_input_byte I b Hd Hin) as [Hp | ->].
      - right. exact (lmb_byte_printable B b Hp).
      - left. by vm_compute.
    Qed.
  End byte_laws.

End line_model.
