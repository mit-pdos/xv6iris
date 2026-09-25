(* ===================================================================== *)
(* GrepFilt.v -- grep's LINE ALGEBRA: the pure facts that make [grep_out] *)
(* a filter in the sense of claude-notes/design/grep-pipes.md SS1 (cut    *)
(* G0).                                                                   *)
(*                                                                        *)
(*   - [lastpart R]: the bytes after R's last newline (all of R if it has *)
(*     none) -- the unfinished line a reader of R is in the middle of.    *)
(*   - [grep_out_app]: what grep owes after [R ++ S] is what it owed      *)
(*     after [R], then what [S] adds from the line [lastpart R] begun:    *)
(*     the [flt_app] law of the filter device, at                         *)
(*     [flt_new R c := gout pat (lastpart R) c].                          *)
(*   - [grep_out_nil], [grep_out_mono], [grep_out_len].                   *)
(*   - THE GATE [grep_out_line]: on a one-line content (the newline half  *)
(*     of [PipesDisc.lshape]), grep of any prefix either prints nothing   *)
(*     or passes the whole line; [grep_out_line_pass] says exactly when.  *)
(*                                                                        *)
(* Additive: nothing imports this file yet.  It sits on [GrepTree] only;  *)
(* [PipesDisc.lshape] is not imported (it would pull the machine in), and *)
(* the gate's premise [oneline L] is lshape's second conjunct verbatim,   *)
(* so a caller holding [Hsh : lshape L] passes [proj2 Hsh].               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import StringBytes LineWords ProgTree GrepTree.

Local Open Scope string_scope.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE UNFINISHED LINE                                               *)
(* ===================================================================== *)

(* [gout]'s line accumulator, run to the end: the line begun at [cur] as
   it stands after [S] *)
Fixpoint lastpart_acc (cur S : bytes) : bytes :=
  match S with
  | [] => cur
  | b :: r => if bdec b wl_nl then lastpart_acc [] r else lastpart_acc (cur ++ [b]) r
  end.
Definition lastpart (R : bytes) : bytes := lastpart_acc [] R.

Lemma lastpart_acc_app (cur R S : bytes) :
  lastpart_acc cur (R ++ S) = lastpart_acc (lastpart_acc cur R) S.
Proof using.
  revert cur. induction R as [| b r IH]; intros cur; [reflexivity |].
  simpl. destruct (bdec b wl_nl); apply IH.
Qed.

Lemma lastpart_app (R S : bytes) : lastpart (R ++ S) = lastpart_acc (lastpart R) S.
Proof using. apply lastpart_acc_app. Qed.

(* a newline-free input only extends the line begun *)
Lemma lastpart_acc_nonl (cur S : bytes) : wl_nl ∉ S -> lastpart_acc cur S = cur ++ S.
Proof using.
  revert cur. induction S as [| b r IH]; intros cur HS; [by rewrite app_nil_r |].
  apply not_elem_of_cons in HS as [Hb HS]. simpl.
  rewrite (bdec_false _ _ (not_eq_sym Hb)), IH by exact HS. by rewrite <- app_assoc.
Qed.

Lemma lastpart_nonl (R : bytes) : wl_nl ∉ R -> lastpart R = R.
Proof using. intros H. unfold lastpart. by rewrite lastpart_acc_nonl. Qed.

(* the unfinished line holds no newline, and is a suffix of what was read *)
Lemma lastpart_acc_free (cur S : bytes) : wl_nl ∉ cur -> wl_nl ∉ lastpart_acc cur S.
Proof using.
  revert cur. induction S as [| b r IH]; intros cur Hc; [exact Hc |].
  simpl. destruct (bdec b wl_nl) eqn:Hb.
  - apply IH. apply not_elem_of_nil.
  - apply IH. rewrite elem_of_app, elem_of_list_singleton. intros [H | H]; [exact (Hc H) |].
    subst b. rewrite (bdec_true _ _ eq_refl) in Hb. discriminate.
Qed.

Lemma lastpart_free (R : bytes) : wl_nl ∉ lastpart R.
Proof using. apply lastpart_acc_free, not_elem_of_nil. Qed.

Lemma lastpart_acc_suffix (cur S : bytes) :
  exists x, cur ++ S = x ++ lastpart_acc cur S.
Proof using.
  revert cur. induction S as [| b r IH]; intros cur.
  - exists []. by rewrite app_nil_r.
  - simpl. destruct (bdec b wl_nl).
    + destruct (IH []) as [x Hx]. exists (cur ++ b :: x). rewrite <- app_assoc. simpl.
      rewrite <- Hx. reflexivity.
    + destruct (IH (cur ++ [b])) as [x Hx]. exists x. rewrite <- Hx, <- app_assoc. reflexivity.
Qed.

Lemma lastpart_suffix (R : bytes) : lastpart R `suffix_of` R.
Proof using. destruct (lastpart_acc_suffix [] R) as [x Hx]. exists x. exact Hx. Qed.

(* ===================================================================== *)
(*  2.  WHAT GREP OWES, ALONG THE INPUT                                   *)
(* ===================================================================== *)

Lemma grep_out_eq_gout (pat S : bytes) : grep_out pat S = gout pat [] S.
Proof using. by rewrite grep_out_gout. Qed.

Lemma gout_app (pat cur R S : bytes) :
  gout pat cur (R ++ S) = gout pat cur R ++ gout pat (lastpart_acc cur R) S.
Proof using.
  revert cur. induction R as [| b r IH]; intros cur; [reflexivity |].
  simpl. destruct (bdec b wl_nl).
  - rewrite IH. by rewrite app_assoc.
  - apply IH.
Qed.

(* THE FILTER LAW ([flt_app] at [flt_new R c := gout pat (lastpart R) c]) *)
Lemma grep_out_app (pat R S : bytes) :
  grep_out pat (R ++ S) = grep_out pat R ++ gout pat (lastpart R) S.
Proof using. rewrite !grep_out_eq_gout. apply gout_app. Qed.

Lemma grep_out_nil (pat : bytes) : grep_out pat [] = [].
Proof using. reflexivity. Qed.

Lemma gout_nil (pat cur : bytes) : gout pat cur [] = [].
Proof using. reflexivity. Qed.

Lemma grep_out_mono (pat R R' : bytes) :
  R `prefix_of` R' -> grep_out pat R `prefix_of` grep_out pat R'.
Proof using. intros [S ->]. rewrite grep_out_app. by eexists. Qed.

Lemma gout_len (pat cur S : bytes) : (length (gout pat cur S) <= length cur + length S)%nat.
Proof using.
  revert cur. induction S as [| b r IH]; intros cur; simpl; [lia |].
  destruct (bdec b wl_nl).
  - rewrite length_app. specialize (IH []). simpl in IH.
    destruct (grep_line_ok pat cur); simpl; [rewrite length_app; simpl |]; lia.
  - specialize (IH (cur ++ [b])). rewrite length_app in IH. simpl in IH. lia.
Qed.

Lemma grep_out_len (pat R : bytes) : (length (grep_out pat R) <= length R)%nat.
Proof using. rewrite grep_out_eq_gout. apply (gout_len pat [] R). Qed.

(* a newline-free input completes no line *)
Lemma gout_nonl (pat cur S : bytes) : wl_nl ∉ S -> gout pat cur S = [].
Proof using.
  revert cur. induction S as [| b r IH]; intros cur HS; [reflexivity |].
  apply not_elem_of_cons in HS as [Hb HS]. simpl.
  rewrite (bdec_false _ _ (not_eq_sym Hb)). by apply IH.
Qed.

Lemma grep_out_nonl (pat D : bytes) : wl_nl ∉ D -> grep_out pat D = [].
Proof using. intros H. rewrite grep_out_eq_gout. by apply gout_nonl. Qed.

(* one complete line: printed whole, or not at all *)
Lemma grep_out_one (pat v : bytes) :
  wl_nl ∉ v ->
  grep_out pat (v ++ [wl_nl]) = if grep_line_ok pat v then v ++ [wl_nl] else [].
Proof using.
  intros Hv. rewrite grep_out_app, grep_out_nonl, lastpart_nonl by exact Hv.
  simpl. rewrite (bdec_true _ _ eq_refl), app_nil_r. by destruct (grep_line_ok pat v).
Qed.

(* ===================================================================== *)
(*  3.  THE GATE                                                          *)
(*                                                                        *)
(*  On a content with at most one newline, its last byte, grep of any     *)
(*  prefix of it prints nothing or the whole line.  It passes exactly     *)
(*  when the prefix is the whole content, the content ends in a newline,  *)
(*  the line before it is at most [grep_maxline] = 1022 bytes, and        *)
(*  [match_re] accepts that line.  An over-long line, a non-matching one, *)
(*  and any strict prefix (no newline yet) all give [].                   *)
(* ===================================================================== *)

(* the newline half of [PipesDisc.lshape], verbatim *)
Definition oneline (L : bytes) : Prop :=
  wl_nl ∉ L \/ exists v, wl_nl ∉ v /\ L = v ++ [wl_nl].

(* a prefix of a one-line content that holds a newline is all of it *)
Lemma oneline_prefix_nl (L D : bytes) :
  oneline L -> D `prefix_of` L -> wl_nl ∈ D ->
  exists v, wl_nl ∉ v /\ L = v ++ [wl_nl] /\ D = L.
Proof using.
  intros [HL | (v & Hv & ->)] [k Hk] Hin.
  - exfalso. apply HL. rewrite Hk. apply elem_of_app. by left.
  - exists v. split; [exact Hv |]. split; [reflexivity |].
    destruct k as [| x k'] using rev_ind.
    + by rewrite app_nil_r in Hk.
    + exfalso. rewrite app_assoc in Hk. apply app_inj_tail in Hk as [Hk _].
      apply Hv. rewrite Hk. apply elem_of_app. by left.
Qed.

Lemma grep_out_line (pat L D : bytes) :
  oneline L -> D `prefix_of` L ->
  grep_out pat D = [] \/ (D = L /\ grep_out pat D = L).
Proof using.
  intros HL HD. destruct (decide (wl_nl ∈ D)) as [Hin | Hnin].
  - destruct (oneline_prefix_nl L D HL HD Hin) as (v & Hv & HLv & ->).
    rewrite HLv, grep_out_one by exact Hv.
    destruct (grep_line_ok pat v); [by right | by left].
  - left. by apply grep_out_nonl.
Qed.

(* ...and exactly when it passes *)
Lemma grep_out_line_pass (pat L D : bytes) :
  oneline L -> D `prefix_of` L ->
  grep_out pat D <> [] <->
  exists v, D = L /\ L = v ++ [wl_nl] /\ (length v <= grep_maxline)%nat /\ match_re pat v = true.
Proof using.
  intros HL HD. split.
  - intros Hne. destruct (decide (wl_nl ∈ D)) as [Hin | Hnin];
      [| by exfalso; apply Hne, grep_out_nonl].
    destruct (oneline_prefix_nl L D HL HD Hin) as (v & Hv & HLv & ->).
    rewrite HLv, grep_out_one in Hne by exact Hv.
    destruct (grep_line_ok pat v) eqn:Hok; [| by exfalso; apply Hne].
    unfold grep_line_ok in Hok. apply andb_true_iff in Hok as [Hlen Hm].
    apply bool_decide_eq_true in Hlen. exists v. done.
  - intros (v & -> & -> & Hlen & Hm).
    assert (Hv : wl_nl ∉ v).
    { intros Hin. destruct HL as [HL | (v' & Hv' & Heq)].
      - apply HL, elem_of_app. by left.
      - apply app_inj_tail in Heq as [<- _]. exact (Hv' Hin). }
    rewrite grep_out_one by exact Hv.
    unfold grep_line_ok. rewrite (bool_decide_true _ Hlen), Hm. simpl.
    intros H. apply (f_equal (@length _)) in H. rewrite length_app in H. simpl in H. lia.
Qed.

(* the gate, as the filter device reads it: what grep prints of a prefix
   of the line is a prefix of the line *)
Lemma grep_out_line_prefix (pat L D : bytes) :
  oneline L -> D `prefix_of` L -> grep_out pat D `prefix_of` L.
Proof using.
  intros HL HD. destruct (grep_out_line pat L D HL HD) as [-> | [_ ->]];
    [apply prefix_nil | reflexivity].
Qed.

(* ===================================================================== *)
(*  4.  DEMOS                                                             *)
(* ===================================================================== *)

Definition gf_nl : bytes := [wl_nl].

(* [lastpart]: after the last newline; all of it if none; [] at a newline *)
Example demo_lastpart :
  map lastpart [sb "ab" ++ gf_nl ++ sb "cd"; sb "abc"; sb "ab" ++ gf_nl; []]
  = [sb "cd"; sb "abc"; []; []].
Proof using. vm_compute. reflexivity. Qed.

(* the filter law split mid-line: [fo] then [o NL bar NL boo NL x] *)
Example demo_grep_out_app :
  let R := sb "fo" in
  let S := sb "o" ++ gf_nl ++ sb "bar" ++ gf_nl ++ sb "boo" ++ gf_nl ++ sb "x" in
  grep_out (sb "o") (R ++ S) = grep_out (sb "o") R ++ gout (sb "o") (lastpart R) S
  /\ grep_out (sb "o") R = []
  /\ gout (sb "o") (lastpart R) S = sb "foo" ++ gf_nl ++ sb "boo" ++ gf_nl.
Proof using. vm_compute. repeat split. Qed.

(* ...and split after a complete line: the owed part is kept, the new
   chunk starts a fresh line *)
Example demo_grep_out_app_nl :
  let R := sb "foo" ++ gf_nl ++ sb "b" in
  let S := sb "oo" ++ gf_nl in
  grep_out (sb "o") R = sb "foo" ++ gf_nl
  /\ lastpart R = sb "b"
  /\ gout (sb "o") (lastpart R) S = sb "boo" ++ gf_nl
  /\ grep_out (sb "o") (R ++ S) = sb "foo" ++ gf_nl ++ sb "boo" ++ gf_nl.
Proof using. vm_compute. repeat split. Qed.

(* a partial last line is owed nothing, even when it matches *)
Example demo_grep_out_partial :
  grep_out (sb "o") (sb "foo" ++ gf_nl ++ sb "boo") = sb "foo" ++ gf_nl.
Proof using. vm_compute. reflexivity. Qed.

(* the gate on every prefix of a one-line content: nothing until the
   newline, then the whole line *)
Definition gf_line : bytes := sb "hello world" ++ gf_nl.
Example demo_gate_pass :
  map (fun k => grep_out (sb "wor") (take k gf_line)) (seq 0 (S (length gf_line)))
  = replicate (length gf_line) [] ++ [gf_line].
Proof using. vm_compute. reflexivity. Qed.

(* a non-matching line: nothing at every prefix *)
Example demo_gate_nomatch :
  map (fun k => grep_out (sb "z") (take k gf_line)) (seq 0 (S (length gf_line)))
  = replicate (S (length gf_line)) [].
Proof using. vm_compute. reflexivity. Qed.

(* the over-long line: 1022 bytes is passed, 1023 is dropped *)
Definition gf_long (k : nat) : bytes := replicate k (ch 97) ++ gf_nl.
Example demo_gate_long :
  grep_out (sb "a") (gf_long 1022) = gf_long 1022
  /\ grep_out (sb "a") (gf_long 1023) = [].
Proof using. vm_compute. split; reflexivity. Qed.

(* monotone, and never longer than the input *)
Example demo_grep_out_mono_len :
  let R := sb "ab" ++ gf_nl ++ sb "c" in
  let R' := R ++ sb "b" ++ gf_nl ++ sb "zz" ++ gf_nl in
  grep_out (sb "b") R = sb "ab" ++ gf_nl
  /\ grep_out (sb "b") R' = sb "ab" ++ gf_nl ++ sb "cb" ++ gf_nl
  /\ Nat.leb (length (grep_out (sb "b") R')) (length R') = true.
Proof using. vm_compute. repeat split. Qed.
