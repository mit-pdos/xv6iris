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
(* G2 adds grep's instance of the filter device (section 5):             *)
(*   - [flt_grep pat]: [grep_out pat] as a [ProgTree.pfilter].            *)
(*   - [grep_filter_conforms]: [grep pat] conforms at [DCopy (flt_grep    *)
(*     pat) h [] L []] on every NUL-free [L] -- the owner's               *)
(*     [grep_go_conforms] re-run with the DEVICE INVARIANT [gf_inv] in    *)
(*     place of the console's owed alternative; [grep_halt_conforms] is   *)
(*     grep at a halted sink (writes answer -1, reads go on).             *)
(*   - [grep_filt_exits]: the exits, at [DCopyEnd (flt_grep pat) h []] or *)
(*     (the sink halted) [DCopyHalt None], the console untouched.         *)
(*                                                                        *)
(* Additive: nothing imports this file yet.  It sits on [GrepTree] and    *)
(* [ProgTreePipes] only;                                                  *)
(* [PipesDisc.lshape] is not imported (it would pull the machine in), and *)
(* the gate's premise [oneline L] is lshape's second conjunct verbatim,   *)
(* so a caller holding [Hsh : lshape L] passes [proj2 Hsh].               *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import StringBytes LineWords ProgTree ProgTreePipes GrepTree.

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

(* ===================================================================== *)
(*  5.  GREP AS A FILTER DEVICE (cut G2, grep-pipes.md SS1)               *)
(*                                                                        *)
(*  [flt_grep pat] is [grep_out pat] as a filter: a chunk [c] read after  *)
(*  [R] owes the lines it completes, [gout pat (lastpart R) c].  grep     *)
(*  conforms at the filter device [DCopy (flt_grep pat) h R S p] under    *)
(*  the DEVICE INVARIANT, in place of the console's owed alternative of   *)
(*  [grep_go_conforms]:                                                   *)
(*    - the pending output is the lines of the buffer still to write,     *)
(*      [p = concat outs];                                                *)
(*    - [gf_inv skip left R]: not skipping, the leftover IS the unfinished *)
(*      line, [left = lastpart R]; skipping, that line is already too     *)
(*      long, [1023 <= length (lastpart R)];                              *)
(*    - the leftover is clean and under 1023 bytes; the input NUL-free.   *)
(*  The owner's [scan_gout] at [T := []] turns a scan into exactly the    *)
(*  device's [flt_new], so every chunking is covered as in the owner's    *)
(*  proof.                                                                *)
(* ===================================================================== *)

Definition flt_grep (pat : bytes) : pfilter :=
  MkFilter (grep_out pat) (fun R c => gout pat (lastpart R) c) (grep_out_app pat) (grep_out_nil pat).

Lemma flt_grep_new (pat R c : bytes) : flt_new (flt_grep pat) R c = gout pat (lastpart R) c.
Proof using. reflexivity. Qed.
Lemma flt_grep_out (pat R : bytes) : flt_out (flt_grep pat) R = grep_out pat R.
Proof using. reflexivity. Qed.

(* ---- the scan, against [lastpart] ------------------------------------ *)

(* on a NUL-free input the scan's leftover is the line accumulator run to
   the end *)
Lemma scan_leftover (pat : bytes) (skip : bool) (cur S : bytes) :
  Forall (fun b => b <> c_nul) S -> (scan pat skip cur S).1.2 = lastpart_acc cur S.
Proof using.
  revert cur skip. induction S as [| b r IH]; intros cur skip HS; [reflexivity |].
  apply Forall_cons_1 in HS as [Hz HS]. simpl.
  destruct (bdec b wl_nl) eqn:Hn; simpl.
  - apply IH, HS.
  - rewrite (bdec_false _ _ Hz); simpl. apply IH, HS.
Qed.

(* ...its flag: kept over a newline-free input, cleared by a newline *)
Lemma scan_skip_nonl (pat : bytes) (skip : bool) (cur S : bytes) :
  Forall (fun b => b <> c_nul) S -> wl_nl ∉ S -> (scan pat skip cur S).2 = skip.
Proof using.
  revert cur. induction S as [| b r IH]; intros cur HS Hnl; [reflexivity |].
  apply Forall_cons_1 in HS as [Hz HS]. apply not_elem_of_cons in Hnl as [Hb Hnl]. simpl.
  rewrite (bdec_false _ _ (not_eq_sym Hb)), (bdec_false _ _ Hz). by apply IH.
Qed.

Lemma scan_skip_nl (pat : bytes) (skip : bool) (cur S : bytes) :
  Forall (fun b => b <> c_nul) S -> wl_nl ∈ S -> (scan pat skip cur S).2 = false.
Proof using.
  revert cur skip. induction S as [| b r IH]; intros cur skip HS Hnl;
    [by apply not_elem_of_nil in Hnl |].
  apply Forall_cons_1 in HS as [Hz HS]. simpl.
  destruct (bdec b wl_nl) eqn:Hn; simpl.
  - destruct (decide (wl_nl ∈ r)) as [Hr | Hr]; [by apply IH | by apply scan_skip_nonl].
  - rewrite (bdec_false _ _ Hz); simpl. apply IH; [exact HS |].
    apply elem_of_cons in Hnl as [Heq | Hr]; [subst b | exact Hr].
    rewrite (bdec_true _ _ eq_refl) in Hn. discriminate.
Qed.

(* after a newline the line begun before it no longer shows *)
Lemma lastpart_acc_nl (cur cur' S : bytes) :
  wl_nl ∈ S -> lastpart_acc cur S = lastpart_acc cur' S.
Proof using.
  revert cur cur'. induction S as [| b r IH]; intros cur cur' Hnl;
    [by apply not_elem_of_nil in Hnl |].
  simpl. destruct (bdec b wl_nl) eqn:Hn; [reflexivity |].
  apply IH. apply elem_of_cons in Hnl as [Heq | Hr]; [subst b | exact Hr].
  rewrite (bdec_true _ _ eq_refl) in Hn. discriminate.
Qed.

(* every line a scan of at most a buffer writes is nonempty and short (a
   halted sink answers -1 only to a count under 2^31) *)
Definition outs_ok (outs : list bytes) : Prop :=
  Forall (fun o => o <> [] /\ (length o <= 1024)%nat) outs.

Lemma scan_outs_ok (pat : bytes) (skip : bool) (cur S : bytes) :
  (length cur + length S <= 1023)%nat -> outs_ok (scan pat skip cur S).1.1.
Proof using.
  unfold outs_ok. revert cur skip. induction S as [| b r IH]; intros cur skip Hlen; [constructor |].
  simpl in Hlen |- *. destruct (bdec b wl_nl).
  - simpl. apply Forall_app. split; [| apply IH; simpl; lia].
    destruct skip; [constructor |].
    destruct (match_re pat cur); [| constructor].
    constructor; [| constructor].
    rewrite length_app. simpl. split; [| lia].
    intros H. apply (f_equal (@length _)) in H. rewrite length_app in H. simpl in H. lia.
  - destruct (bdec b c_nul); simpl; [constructor |]. apply IH. rewrite length_app. simpl. lia.
Qed.

(* ---- the device invariant --------------------------------------------- *)

Definition gf_inv (skip : bool) (left R : bytes) : Prop :=
  if skip then (1023 <= length (lastpart R))%nat else left = lastpart R.

(* what a scan writes is what the device's read added *)
Lemma gf_owed (pat : bytes) (skip : bool) (left R c : bytes) :
  gf_inv skip left R -> Forall (fun b => b <> c_nul) c -> (length left + length c <= 1023)%nat ->
  concat (scan pat skip left c).1.1 = gout pat (lastpart R) c.
Proof using.
  intros Hinv Hnul Hlen.
  pose proof (scan_gout pat skip left c [] Hnul Hlen) as Hg.
  rewrite gout_s_nil, !app_nil_r in Hg. rewrite Hg.
  unfold gout_s, gf_inv in *. destruct skip.
  - symmetry. by apply gout_long.
  - by subst left.
Qed.

(* ...and the invariant holds after it *)
Lemma gf_inv_step (pat : bytes) (skip : bool) (left R c : bytes) :
  gf_inv skip left R -> Forall (fun b => b <> c_nul) c ->
  gf_inv (scan pat skip left c).2 (scan pat skip left c).1.2 (R ++ c).
Proof using.
  intros Hinv Hnul. unfold gf_inv. rewrite lastpart_app, scan_leftover by exact Hnul.
  destruct (decide (wl_nl ∈ c)) as [Hnl | Hnl].
  - rewrite scan_skip_nl by assumption. simpl. by apply lastpart_acc_nl.
  - rewrite scan_skip_nonl by assumption. unfold gf_inv in Hinv. destruct skip; simpl in *.
    + rewrite lastpart_acc_nonl, length_app by exact Hnl. lia.
    + by subst left.
Qed.

(* ...and a full buffer, reset, leaves grep skipping a line already too
   long *)
Lemma gf_inv_reset (skip : bool) (left R : bytes) :
  gf_inv skip left R -> (1023 <= length left)%nat -> gf_inv true [] R.
Proof using.
  unfold gf_inv. intros Hinv Hl. destruct skip; simpl in *; [exact Hinv | subst left; exact Hl].
Qed.

(* ---- grep at a HALTED sink: writes answer -1, reads go on ------------- *)

Lemma grep_halt_conforms (pat : bytes) (alts : list bytes) files paths (rest : proc) :
  conforms (copy_env (DCopyHalt None) alts files paths) rest ->
  forall oS skip outs left, (length left < 1023)%nat -> outs_ok outs ->
    conforms (copy_env (DCopyHalt oS) alts files paths) (grep_go pat 0 skip outs left rest).
Proof using.
  intros Hrest. cofix CIH. intros oS skip outs left Hlen Hok.
  rewrite grep_go_unfold. destruct outs as [| o os].
  - destruct oS as [S |].
    + eapply cf_read_copy_halt with (d := 1%nat) (S := S).
      { unfold grep_room, grep_bufsz. lia. }
      { reflexivity. }
      { apply copy_env_fd0. }
      { apply copy_env_dev1. }
      2: { rewrite copy_env_set. exact Hrest. }
      intros c S' (HS & Hclen & _) Hne. rewrite copy_env_set.
      destruct c as [| b c']; [by destruct Hne |]. cbv beta iota zeta.
      assert (Hbuf : (length ([] : bytes) + length (left ++ b :: c') <= 1023)%nat)
        by (rewrite length_app; unfold grep_room, grep_bufsz in Hclen; simpl in Hclen |- *; lia).
      destruct (decide _) as [Hfull | Hroom].
      * apply CIH; [simpl; lia | exact (scan_outs_ok _ _ _ _ Hbuf)].
      * apply CIH; [unfold grep_bufsz in Hroom; lia | exact (scan_outs_ok _ _ _ _ Hbuf)].
    + eapply cf_read_copy_halt_end with (d := 1%nat).
      { unfold grep_room, grep_bufsz. lia. }
      { reflexivity. }
      { apply copy_env_fd0. }
      { apply copy_env_dev1. }
      exact Hrest.
  - unfold outs_ok in Hok. apply Forall_cons_1 in Hok as [[Hne Ho] Hok].
    eapply cf_write_copy_halt with (d := 1%nat) (oS := oS).
    { exact Hne. }
    { change (2 ^ 31)%Z with 2147483648%Z. lia. }
    { reflexivity. }
    { apply copy_env_fd1. }
    { apply copy_env_dev1. }
    apply CIH; [exact Hlen | exact Hok].
Qed.

(* ---- grep at the filter device ---------------------------------------- *)

Lemma grep_filt_go_conforms (pat : bytes) (h : bool) (alts : list bytes) files paths (rest : proc) :
  conforms (copy_env (DCopyEnd (flt_grep pat) h []) alts files paths) rest ->
  conforms (copy_env (DCopyHalt None) alts files paths) rest ->
  forall skip outs left R S,
    outs_ok outs -> Forall clean left -> (length left < 1023)%nat -> grep_ok S ->
    gf_inv skip left R ->
    conforms (copy_env (DCopy (flt_grep pat) h R S (concat outs)) alts files paths)
             (grep_go pat 0 skip outs left rest).
Proof using.
  intros Hend Hhalt. cofix CIH. intros skip outs left R S Hok Hcl Hlen HS Hinv.
  rewrite grep_go_unfold. destruct outs as [| o os]; cbn [concat].
  - (* the read, at the room left: at least one byte *)
    eapply cf_read_copy with (d := 1%nat) (F := flt_grep pat) (h := h) (Rr := R) (S := S) (p := []).
    { unfold grep_room, grep_bufsz. lia. }
    { reflexivity. }
    { apply copy_env_fd0. }
    { apply copy_env_dev1. }
    2: { (* end of file: nothing is pending *) rewrite copy_env_set. exact Hend. }
    intros c S' (HSc & Hclen & _) Hne. rewrite copy_env_set, flt_grep_new, app_nil_l.
    destruct c as [| b c']; [by destruct Hne |]. cbv beta iota zeta.
    subst S. unfold grep_ok in HS. apply Forall_app in HS as [Hnul HS'].
    assert (Hbuf : (length left + length (b :: c') <= 1023)%nat)
      by (unfold grep_room, grep_bufsz in Hclen; lia).
    rewrite scan_clean_app by exact Hcl. simpl app.
    rewrite <- (gf_owed pat skip left R (b :: c') Hinv Hnul Hbuf).
    pose proof (gf_inv_step pat skip left R (b :: c') Hinv Hnul) as Hinv'.
    pose proof (scan_outs_ok pat skip left (b :: c') Hbuf) as Hok'.
    destruct (decide (grep_bufsz - 1 <= length (scan pat skip left (b :: c')).1.2)%nat) as [Hfull | Hroom].
    + (* the buffer is full and holds no newline: skip the line *)
      apply CIH; [exact Hok' | constructor | simpl; lia | exact HS' |].
      apply (gf_inv_reset _ _ _ Hinv'). unfold grep_bufsz in Hfull. lia.
    + apply CIH; [exact Hok' | | unfold grep_bufsz in Hroom; lia | exact HS' | exact Hinv'].
      apply scan_leftover_clean; [exact Hcl | exact Hnul].
  - (* a line: the head of what is pending *)
    unfold outs_ok in Hok. apply Forall_cons_1 in Hok as [[Hne Ho] Hok].
    eapply cf_write_copy with (d := 1%nat) (F := flt_grep pat) (h := h) (Rr := R) (S := S)
      (p := o ++ concat os).
    { exact Hne. }
    { reflexivity. }
    { apply copy_env_fd1. }
    { apply copy_env_dev1. }
    { by eexists. }
    + rewrite drop_app_length, copy_env_set.
      apply CIH; [exact Hok | exact Hcl | exact Hlen | exact HS | exact Hinv].
    + intros _. rewrite copy_env_set.
      apply grep_halt_conforms; [exact Hhalt | exact Hlen | exact Hok].
Qed.

(* THE FILTER CONFORMANCE: [grep pat] with its input a pipe's read end and
   its output the filter device's sink owes exactly [grep_out pat] of what
   it read, at every chunking; the console on descriptor 2 is never
   written *)
Theorem grep_filter_conforms (pat : bytes) (h : bool) (L : bytes) (alts : list bytes) files paths :
  grep_ok L -> [] ∈ alts ->
  conforms (copy_env (DCopy (flt_grep pat) h [] L []) alts files paths) (grep_tree [sb "grep"; pat]).
Proof using.
  intros HL Hnil. unfold grep_tree. simpl drop.
  apply (grep_filt_go_conforms pat h alts files paths (exit_ 0)
           (copy_env_exit (DCopyEnd (flt_grep pat) h []) alts files paths 0 Hnil eq_refl)
           (copy_env_exit (DCopyHalt None) alts files paths 0 Hnil I)
           false [] [] [] L); [constructor | constructor | simpl; lia | exact HL | reflexivity].
Qed.

(* ---- the exits --------------------------------------------------------- *)

Inductive gx_st (pat : bytes) (h : bool) (alts : list bytes) files paths : penv -> proc -> Prop :=
  | gx_run R S p skip outs left :
      gx_st pat h alts files paths (copy_env (DCopy (flt_grep pat) h R S p) alts files paths)
        (grep_go pat 0 skip outs left (exit_ 0))
  | gx_end p :
      gx_st pat h alts files paths (copy_env (DCopyEnd (flt_grep pat) h p) alts files paths) (exit_ 0)
  | gx_halt oS skip outs left : h = true ->
      gx_st pat h alts files paths (copy_env (DCopyHalt oS) alts files paths)
        (grep_go pat 0 skip outs left (exit_ 0))
  | gx_halt_end : h = true ->
      gx_st pat h alts files paths (copy_env (DCopyHalt None) alts files paths) (exit_ 0).

Definition grep_exit (pat : bytes) (h : bool) (alts : list bytes) files paths (E' : penv) : Prop :=
  [] ∈ alts
  /\ (E' = copy_env (DCopyEnd (flt_grep pat) h []) alts files paths
      \/ (h = true /\ E' = copy_env (DCopyHalt None) alts files paths)).

Lemma gx_st_closed (pat : bytes) (h : bool) (alts : list bytes) files paths (E : penv) (t : proc) :
  gx_st pat h alts files paths E t -> re_step (grep_exit pat h alts files paths) (gx_st pat h alts files paths) E t.
Proof using.
  intros Hst. destruct Hst as [R S p skip outs left | p | oS skip outs left Hh | Hh].
  - rewrite grep_go_unfold. destruct outs as [| o os].
    + (* the read *)
      cbn [re_step]. intros d Hd _. rewrite copy_env_fd0 in Hd. injection Hd as <-.
      rewrite copy_env_dev1.
      split; [intros; discriminate |]. split; [intros; discriminate |].
      split; [intros; discriminate |]. split; [| repeat split; intros; discriminate].
      intros F' h' R' S' p' _ Heq. injection Heq as <- <- <- <- <-. split.
      * intros c S'' _ Hc. rewrite copy_env_set. destruct c as [| b c']; [done |].
        cbv beta iota zeta. destruct (decide _); apply gx_run.
      * rewrite copy_env_set. apply gx_end.
    + (* a line written *)
      cbn [re_step]. intros d Hd. rewrite copy_env_fd1 in Hd. injection Hd as <-.
      rewrite copy_env_dev1.
      split; [intros _; split; apply gx_run |].
      do 4 (split; [intros; discriminate |]).
      split; [| repeat split; intros; discriminate].
      intros F' h' R' S' p' _ _ Heq _. injection Heq as <- <- <- <- <-. split.
      * rewrite copy_env_set. apply gx_run.
      * intros ->. rewrite copy_env_set. by apply gx_halt.
  - cbn [exit_ re_step]. intros Hdr. split.
    { pose proof (Hdr 0%nat) as H0. rewrite copy_env_dev0 in H0. exact H0. }
    left.
    specialize (Hdr 1%nat). rewrite copy_env_dev1 in Hdr. cbn in Hdr. by subst p.
  - rewrite grep_go_unfold. destruct outs as [| o os].
    + cbn [re_step]. intros d Hd _. rewrite copy_env_fd0 in Hd. injection Hd as <-.
      rewrite copy_env_dev1. destruct oS as [S |].
      * do 5 (split; [intros; discriminate |]). split; [| intros; discriminate].
        intros S0 _ Heq. injection Heq as <-. split.
        -- intros c S'' _ Hc. rewrite copy_env_set. destruct c as [| b c']; [done |].
           cbv beta iota zeta. destruct (decide _); by apply gx_halt.
        -- rewrite copy_env_set. by apply gx_halt_end.
      * do 6 (split; [intros; discriminate |]). intros _ _. by apply gx_halt_end.
    + cbn [re_step]. intros d Hd. rewrite copy_env_fd1 in Hd. injection Hd as <-.
      rewrite copy_env_dev1.
      split; [intros _; split; by apply gx_halt |].
      do 6 (split; [intros; discriminate |]).
      intros oS' _ _ _ _. by apply gx_halt.
  - cbn [exit_ re_step]. intros Hdr. split.
    { pose proof (Hdr 0%nat) as H0. rewrite copy_env_dev0 in H0. exact H0. }
    right. split; [exact Hh | reflexivity].
Qed.

(* grep at the filter device exits having read its input to the end and
   written all it owed, or with its sink halted and its input read to the
   end; either way the console on descriptor 2 is untouched *)
Theorem grep_filt_exits (pat : bytes) (h : bool) (L : bytes) (alts : list bytes) files paths (E' : penv) :
  reach_exit (copy_env (DCopy (flt_grep pat) h [] L []) alts files paths) (grep_tree [sb "grep"; pat]) E' ->
  [] ∈ alts
  /\ (E' = copy_env (DCopyEnd (flt_grep pat) h []) alts files paths
      \/ (h = true /\ E' = copy_env (DCopyHalt None) alts files paths)).
Proof using.
  intros Hr.
  apply (reach_exit_inv (grep_exit pat h alts files paths) (gx_st pat h alts files paths)
           (gx_st_closed pat h alts files paths) _ _ _ Hr).
  exact (gx_run pat h alts files paths [] L [] false [] []).
Qed.

(* ===================================================================== *)
(*  6.  DEMOS OF THE INSTANCE                                             *)
(* ===================================================================== *)

Lemma gf_line_ok : grep_ok gf_line.
Proof using. unfold grep_ok. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* a matching line: the device owes the whole line, and grep conforms *)
Example demo_grep_filter_match :
  flt_out (flt_grep (sb "wor")) gf_line = gf_line
  /\ conforms (copy_env (DCopy (flt_grep (sb "wor")) true [] gf_line []) [[]] (fun _ => None) [])
       (grep_tree [sb "grep"; sb "wor"]).
Proof using.
  split; [vm_compute; reflexivity |].
  apply grep_filter_conforms; [exact gf_line_ok | by left].
Qed.

(* a non-matching line: the device owes nothing, and grep conforms *)
Example demo_grep_filter_nomatch :
  flt_out (flt_grep (sb "z")) gf_line = []
  /\ conforms (copy_env (DCopy (flt_grep (sb "z")) false [] gf_line []) [[]] (fun _ => None) [])
       (grep_tree [sb "grep"; sb "z"]).
Proof using.
  split; [vm_compute; reflexivity |].
  apply grep_filter_conforms; [exact gf_line_ok | by left].
Qed.

(* the chunk laws at a line read in two pieces: nothing is owed until the
   newline, then the line *)
Example demo_grep_filter_chunks :
  let F := flt_grep (sb "wor") in
  flt_new F [] (sb "hello w") = []
  /\ flt_new F (sb "hello w") (sb "orld" ++ gf_nl) = gf_line.
Proof using. vm_compute. split; reflexivity. Qed.
