(* ===================================================================== *)
(* PipeBothNPure.v -- THE N-WRITER BLOCK, PURE (design:                   *)
(* claude-notes/design/pipes-general.md SS2.1-SS2.3, cut C5).              *)
(*                                                                        *)
(* [PipeBothPure]'s two-writer merge, generalised to any finite set of    *)
(* writers.  Nothing in the application imports it yet.                   *)
(*                                                                        *)
(*   1. THE MERGE BY WRITER INDEX.  Writers range over an abstract type   *)
(*      [W] with decidable equality; a selector is a [list W], one entry *)
(*      per byte on the wire, naming the writer that wrote it.            *)
(*      [mergeN src sel] consumes each writer's source from the front, as *)
(*      [PipeDisc.pmerge] does for [W := bool]; [pendN md sel] is the     *)
(*      block so far, read at the FIRED sources [md] (a writer that has   *)
(*      not fired reads the empty source).  [cntN sel w] is writer [w]'s  *)
(*      cursor and [sel_wfN] says no cursor runs past its source.         *)
(*   2. THE LAWS: a byte at a cursor appends exactly that byte            *)
(*      ([mergeN_snoc]), the merge only reads the writers it names        *)
(*      ([mergeN_local]), and a selector that exhausts every source is a *)
(*      [PipesDisc.merge_all] of the sources ([mergeN_merge_all]).        *)
(*   3. COMPATIBILITY AND COMPLETION: [compatN RUN md] says the fired     *)
(*      sources extend to a complete run; [pendN_complete] is the         *)
(*      generalisation of [PipeBoth.pblk2_wit]: a partial block whose     *)
(*      fired sources are compatible is a prefix of a merge of a          *)
(*      complete run ([blkN RUN]), and a block with every writer fired   *)
(*      and exhausted IS one ([pendN_file]).                              *)
(*   4. THE PIPELINE'S WRITERS: [wid := WSh k | WLeft k | WLast] (sh node *)
(*      k, the left stage k, the last cat), [wids n] in the order         *)
(*      sigma_0, lambda_0, .., sigma_(n-1), lambda_(n-1), rho, and the   *)
(*      per-writer runs [line_runV] -- [PipesDisc.line_run] with every    *)
(*      silent writer's empty stream in place -- with the bridge          *)
(*      [line_runV_blocks]: a merge of a per-writer run is one of         *)
(*      [PipesDisc.line_blocks].  [pipesN_wit] is the admissible          *)
(*      alternative of [PipesDisc.pipes_lm] a partial block is a prefix   *)
(*      of.                                                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel PipeDisc.
Require Import ProgTree ProgTreePipes PipesPair PipesDisc.
Require Import PipesDiscDec.      (* [ptermb], the prefix test of a terminal block *)
From stdpp Require Import list.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  THE MERGE BY WRITER INDEX                                         *)
(* ===================================================================== *)

Section mergeN.
  Context {W : Type} `{!EqDecision W}.

  (* the source function with writer [w]'s source replaced *)
  Definition supd (src : W -> bytes) (w : W) (r : bytes) : W -> bytes :=
    fun w' => if decide (w' = w) then r else src w'.

  (* [PipeDisc.pmerge] by writer index: each entry of the selector takes
     the next byte of its writer's source; a source that has run out ends
     the merge (never reached at a well-formed selector) *)
  Fixpoint mergeN (src : W -> bytes) (sel : list W) : bytes :=
    match sel with
    | [] => []
    | w :: s =>
        match src w with
        | [] => []
        | b :: r => b :: mergeN (supd src w r) s
        end
    end.

  (* writer [w]'s cursor: how many bytes of the block are its own *)
  Fixpoint cntN (sel : list W) (w : W) : nat :=
    match sel with
    | [] => 0
    | x :: s => (if decide (x = w) then 1 else 0) + cntN s w
    end.

  (* no cursor runs past its source *)
  Definition sel_wfN (src : W -> bytes) (sel : list W) : Prop :=
    forall w, cntN sel w <= length (src w).

  (* the FIRED sources: [md w = Some s] once writer [w] has fixed its
     source [s]; an unfired writer reads the empty source *)
  Definition srcN (md : W -> option bytes) : W -> bytes :=
    fun w => default [] (md w).

  (* the block so far *)
  Definition pendN (md : W -> option bytes) (sel : list W) : bytes :=
    mergeN (srcN md) sel.

  (* what is left of every source after the selector *)
  Definition restN (src : W -> bytes) (sel : list W) : W -> bytes :=
    fun w => drop (cntN sel w) (src w).

  (* ---- the counter ---- *)

  Lemma cntN_app s1 s2 w : cntN (s1 ++ s2) w = cntN s1 w + cntN s2 w.
  Proof using. induction s1 as [| x s IH]; cbn [cntN app]; [reflexivity | rewrite IH; lia]. Qed.

  Lemma cntN_single x w : cntN [x] w = if decide (x = w) then 1 else 0.
  Proof using. cbn [cntN]. lia. Qed.

  Lemma cntN_self_snoc s w : cntN (s ++ [w]) w = S (cntN s w).
  Proof using. rewrite cntN_app, cntN_single, decide_True by reflexivity. lia. Qed.

  Lemma cntN_other_snoc s w w' : w' <> w -> cntN (s ++ [w]) w' = cntN s w'.
  Proof using. intros Hne. rewrite cntN_app, cntN_single, decide_False by congruence. lia. Qed.

  Lemma cntN_elem s w : w ∈ s <-> cntN s w <> 0.
  Proof using.
    induction s as [| x s IH]; cbn [cntN].
    - split; [intros H; by apply elem_of_nil in H | lia].
    - rewrite elem_of_cons. destruct (decide (x = w)) as [-> | Hne]; split.
      + lia.
      + by left.
      + intros [-> | H]; [congruence | apply IH in H; lia].
      + intros H. right. apply IH. lia.
  Qed.

  Lemma cntN_nil_notin s w : w ∉ s -> cntN s w = 0.
  Proof using. intros Hn. destruct (decide (cntN s w = 0)) as [? | H]; [done |]. by apply cntN_elem in H. Qed.

  Lemma cntN_length s : forall w, cntN s w <= length s.
  Proof using. induction s as [| x s IH]; intros w; cbn [cntN length]; [lia |]. specialize (IH w). case_decide; lia. Qed.

  (* ---- extensionality: the merge reads its sources pointwise ---- *)

  Lemma mergeN_ext (f g : W -> bytes) sel :
    (forall w, f w = g w) -> mergeN f sel = mergeN g sel.
  Proof using.
    revert f g. induction sel as [| w s IH]; intros f g Hfg; [reflexivity |].
    cbn [mergeN]. rewrite (Hfg w). destruct (g w) as [| b r]; [reflexivity |].
    f_equal. apply IH. intros w'. unfold supd. case_decide; [reflexivity | apply Hfg].
  Qed.

  (* THE MERGE ONLY READS THE WRITERS IT NAMES *)
  Lemma mergeN_local (f g : W -> bytes) sel :
    (forall w, w ∈ sel -> f w = g w) -> mergeN f sel = mergeN g sel.
  Proof using.
    revert f g. induction sel as [| w s IH]; intros f g Hfg; [reflexivity |].
    cbn [mergeN]. rewrite (Hfg w (elem_of_list_here w s)).
    destruct (g w) as [| b r]; [reflexivity |].
    f_equal. apply IH. intros w' Hw'. unfold supd. case_decide; [reflexivity |].
    apply Hfg. by apply elem_of_list_further.
  Qed.

  Lemma sel_wfN_cons_inv src w s :
    sel_wfN src (w :: s) ->
    exists b r, src w = b :: r /\ sel_wfN (supd src w r) s.
  Proof using.
    intros Hwf. pose proof (Hwf w) as Hw. cbn [cntN] in Hw.
    rewrite decide_True in Hw by reflexivity.
    destruct (src w) as [| b r] eqn:Hs; [cbn [length] in Hw; lia |].
    exists b, r. split; [reflexivity |].
    intros w'. specialize (Hwf w'). cbn [cntN] in Hwf. unfold supd.
    destruct (decide (w' = w)) as [-> | Hne].
    - rewrite decide_True in Hwf by reflexivity. rewrite Hs in Hwf. cbn [length] in Hwf. lia.
    - rewrite decide_False in Hwf by congruence. lia.
  Qed.

  Lemma restN_cons src w b r s :
    src w = b :: r -> forall w', restN (supd src w r) s w' = restN src (w :: s) w'.
  Proof using.
    intros Hs w'. unfold restN, supd. cbn [cntN].
    destruct (decide (w' = w)) as [-> | Hne].
    - rewrite decide_True by reflexivity. rewrite Hs. reflexivity.
    - rewrite decide_False by congruence. reflexivity.
  Qed.

  (* THE MERGE SPLITS at a well-formed first part *)
  Lemma mergeN_app src s1 s2 :
    sel_wfN src s1 -> mergeN src (s1 ++ s2) = mergeN src s1 ++ mergeN (restN src s1) s2.
  Proof using.
    revert src. induction s1 as [| w s IH]; intros src Hwf.
    - cbn [app mergeN]. apply mergeN_ext. intros w. reflexivity.
    - destruct (sel_wfN_cons_inv src w s Hwf) as (b & r & Hs & Hwf').
      cbn [app mergeN]. rewrite Hs. cbn [app]. f_equal.
      rewrite (IH _ Hwf'). f_equal. apply mergeN_ext. exact (restN_cons src w b r s Hs).
  Qed.

  Lemma sel_wfN_app_l src s1 s2 : sel_wfN src (s1 ++ s2) -> sel_wfN src s1.
  Proof using. intros H w. specialize (H w). rewrite cntN_app in H. lia. Qed.

  Lemma sel_wfN_prefix src s1 s2 : s1 `prefix_of` s2 -> sel_wfN src s2 -> sel_wfN src s1.
  Proof using. intros [z ->]. apply sel_wfN_app_l. Qed.

  (* THE BYTE STEP: a byte at writer [w]'s cursor appends exactly it *)
  Lemma mergeN_snoc src sel w b :
    sel_wfN src sel -> src w !! cntN sel w = Some b ->
    mergeN src (sel ++ [w]) = mergeN src sel ++ [b].
  Proof using.
    intros Hwf Hb. rewrite (mergeN_app src sel [w] Hwf). f_equal.
    cbn [mergeN]. unfold restN. rewrite (drop_S (src w) b (cntN sel w) Hb). reflexivity.
  Qed.

  Lemma sel_wfN_snoc src sel w :
    sel_wfN src sel -> cntN sel w < length (src w) -> sel_wfN src (sel ++ [w]).
  Proof using.
    intros Hwf Hlt w'. destruct (decide (w' = w)) as [-> | Hne].
    - rewrite cntN_self_snoc. lia.
    - rewrite cntN_other_snoc by exact Hne. apply Hwf.
  Qed.

  Lemma mergeN_length src sel : sel_wfN src sel -> length (mergeN src sel) = length sel.
  Proof using.
    revert src. induction sel as [| w s IH]; intros src Hwf; [reflexivity |].
    destruct (sel_wfN_cons_inv src w s Hwf) as (b & r & Hs & Hwf').
    cbn [mergeN length]. rewrite Hs. cbn [length]. rewrite (IH _ Hwf'). reflexivity.
  Qed.

  Lemma mergeN_prefix src s1 s2 :
    s1 `prefix_of` s2 -> sel_wfN src s2 -> mergeN src s1 `prefix_of` mergeN src s2.
  Proof using.
    intros [z ->] Hwf. rewrite (mergeN_app src s1 z (sel_wfN_app_l src s1 z Hwf)).
    by eexists.
  Qed.

  (* the merge preserves a byte property every source has *)
  Lemma mergeN_forall (P : bv 8 -> Prop) src sel :
    (forall w, w ∈ sel -> Forall P (src w)) -> Forall P (mergeN src sel).
  Proof using.
    revert src. induction sel as [| w s IH]; intros src HP; [constructor |].
    cbn [mergeN]. pose proof (HP w (elem_of_list_here w s)) as Hw.
    destruct (src w) as [| b r] eqn:Hs; [constructor |].
    apply Forall_cons_1 in Hw as [Hb Hr]. constructor; [exact Hb |].
    apply IH. intros w' Hw'. unfold supd. case_decide; [exact Hr |].
    apply HP. by apply elem_of_list_further.
  Qed.

  (* ===================================================================== *)
  (*  2.  A SELECTOR THAT EXHAUSTS EVERY SOURCE IS A [merge_all]           *)
  (* ===================================================================== *)

  Lemma map_supd_insert (src : W -> bytes) (ws : list W) (i : nat) (w : W) (r : bytes) :
    NoDup ws -> ws !! i = Some w ->
    <[i := r]> (src <$> ws) = supd src w r <$> ws.
  Proof using.
    intros Hnd Hi. apply list_eq. intros j.
    rewrite list_lookup_fmap. destruct (decide (j = i)) as [-> | Hne].
    - rewrite list_lookup_insert by (rewrite length_fmap; exact (lookup_lt_Some _ _ _ Hi)).
      rewrite Hi. cbn. unfold supd. rewrite decide_True by reflexivity. reflexivity.
    - rewrite list_lookup_insert_ne by congruence. rewrite list_lookup_fmap.
      destruct (ws !! j) as [w' |] eqn:Hj; [| reflexivity]. cbn. unfold supd.
      rewrite decide_False; [reflexivity |]. intros ->.
      apply Hne. exact (NoDup_lookup ws j i w Hnd Hj Hi).
  Qed.

  (* THE EXACT MERGE: every writer of [ws] exhausted, no other named *)
  Lemma mergeN_merge_all (ws : list W) (src : W -> bytes) (sel : list W) :
    NoDup ws -> (forall w, w ∈ sel -> w ∈ ws) ->
    (forall w, w ∈ ws -> cntN sel w = length (src w)) ->
    merge_all (src <$> ws) (mergeN src sel).
  Proof using.
    intros Hnd. revert src. induction sel as [| w s IH]; intros src Hin Hcnt.
    - cbn [mergeN]. apply ma_done. apply Forall_fmap. apply Forall_forall.
      intros w Hw. specialize (Hcnt w Hw). cbn [cntN] in Hcnt. cbn.
      by apply nil_length_inv.
    - assert (Hw : w ∈ ws) by (apply Hin; apply elem_of_list_here).
      pose proof (Hcnt w Hw) as Hcw. cbn [cntN] in Hcw.
      rewrite decide_True in Hcw by reflexivity.
      destruct (src w) as [| b r] eqn:Hs; [cbn [length] in Hcw; lia |].
      destruct (elem_of_list_lookup_1 ws w Hw) as (i & Hi).
      assert (Hm : merge_all (supd src w r <$> ws) (mergeN (supd src w r) s)).
      { apply IH.
        - intros w' Hw'. apply Hin. by apply elem_of_list_further.
        - intros w' Hw'. specialize (Hcnt w' Hw'). cbn [cntN] in Hcnt. unfold supd.
          destruct (decide (w' = w)) as [-> | Hne].
          + rewrite decide_True in Hcnt by reflexivity. rewrite Hs in Hcnt.
            cbn [length] in Hcnt. lia.
          + rewrite decide_False in Hcnt by congruence. lia. }
      rewrite <- (map_supd_insert src ws i w r Hnd Hi) in Hm.
      cbn [mergeN]. rewrite Hs.
      refine (ma_take _ i b r _ _ Hm).
      rewrite list_lookup_fmap, Hi. cbn. rewrite Hs. reflexivity.
  Qed.

  (* ---- the padding: every writer's remaining bytes, in writer order ---- *)
  Definition padN (ws : list W) (src : W -> bytes) (sel : list W) : list W :=
    sel ++ concat ((fun w => replicate (length (src w) - cntN sel w) w) <$> ws).

  Lemma cntN_replicate n x w : cntN (replicate n x) w = if decide (x = w) then n else 0.
  Proof using. induction n as [| n IH]; cbn [replicate cntN]; [by case_decide | rewrite IH; case_decide; lia]. Qed.

  Lemma cntN_concat_rep (ws : list W) (f : W -> nat) (w : W) :
    NoDup ws ->
    cntN (concat ((fun x => replicate (f x) x) <$> ws)) w = if decide (w ∈ ws) then f w else 0.
  Proof using.
    induction ws as [| x ws IH]; intros Hnd.
    - cbn. rewrite decide_False; [reflexivity | apply not_elem_of_nil].
    - apply NoDup_cons in Hnd as [Hx Hnd].
      rewrite fmap_cons. cbn [concat]. rewrite cntN_app, cntN_replicate, (IH Hnd).
      destruct (decide (x = w)) as [-> | Hne].
      + rewrite decide_False by exact Hx. rewrite decide_True by apply elem_of_list_here. lia.
      + destruct (decide (w ∈ ws)) as [Hw | Hw].
        * rewrite decide_True by (by apply elem_of_list_further). lia.
        * rewrite decide_False; [lia |]. rewrite elem_of_cons. intros [-> | H]; [congruence | done].
  Qed.

  Lemma padN_cnt (ws : list W) (src : W -> bytes) (sel : list W) w :
    NoDup ws -> sel_wfN src sel -> w ∈ ws -> cntN (padN ws src sel) w = length (src w).
  Proof using.
    intros Hnd Hwf Hw. unfold padN. rewrite cntN_app, (cntN_concat_rep ws _ w Hnd).
    rewrite decide_True by exact Hw. specialize (Hwf w). lia.
  Qed.

  Lemma padN_in (ws : list W) (src : W -> bytes) (sel : list W) w :
    (forall x, x ∈ sel -> x ∈ ws) -> w ∈ padN ws src sel -> w ∈ ws.
  Proof using.
    intros Hin Hw. unfold padN in Hw. apply elem_of_app in Hw as [Hw | Hw]; [by apply Hin |].
    apply elem_of_list_In in Hw. apply in_concat in Hw as (l & Hl & Hwl).
    apply elem_of_list_In in Hl. apply elem_of_list_In in Hwl.
    apply elem_of_list_fmap in Hl as (x & -> & Hx).
    apply elem_of_replicate in Hwl as [-> _]. exact Hx.
  Qed.

  Lemma padN_wf (ws : list W) (src : W -> bytes) (sel : list W) :
    NoDup ws -> (forall x, x ∈ sel -> x ∈ ws) -> sel_wfN src sel ->
    sel_wfN src (padN ws src sel).
  Proof using.
    intros Hnd Hin Hwf w. destruct (decide (w ∈ ws)) as [Hw | Hw].
    - rewrite (padN_cnt ws src sel w Hnd Hwf Hw). lia.
    - rewrite cntN_nil_notin; [lia |]. intros Hp. apply Hw. exact (padN_in ws src sel w Hin Hp).
  Qed.

  (* THE COMPLETION: a well-formed partial block is a prefix of the merge
     of its sources taken whole *)
  Lemma mergeN_complete (ws : list W) (src : W -> bytes) (sel : list W) :
    NoDup ws -> (forall x, x ∈ sel -> x ∈ ws) -> sel_wfN src sel ->
    exists b, merge_all (src <$> ws) b /\ mergeN src sel `prefix_of` b.
  Proof using.
    intros Hnd Hin Hwf. exists (mergeN src (padN ws src sel)). split.
    - apply mergeN_merge_all; [exact Hnd | |].
      + intros w Hw. exact (padN_in ws src sel w Hin Hw).
      + intros w Hw. exact (padN_cnt ws src sel w Hnd Hwf Hw).
    - apply mergeN_prefix; [unfold padN; by eexists |].
      exact (padN_wf ws src sel Hnd Hin Hwf).
  Qed.

  (* ===================================================================== *)
  (*  3.  COMPATIBILITY, AND THE BLOCKS OF THE RUNS                         *)
  (* ===================================================================== *)

  (* THE FIRED SOURCES EXTEND TO A COMPLETE RUN.  [RUN] is the set of
     complete source vectors the model admits (at the pipeline:
     [line_runV] read writer by writer). *)
  Definition compatN (RUN : (W -> bytes) -> Prop) (md : W -> option bytes) : Prop :=
    exists src, RUN src /\ forall w s, md w = Some s -> src w = s.

  (* ...AND THE FAMILY'S INVARIANT, which is sharper (lane PIPES-C7): the
     fired sources ARE a complete run once every writer that has not
     committed is read as SILENT.  [compatN] lets an uncommitted writer
     take any source in the completing run, and that is too weak to be
     kept: a state whose committed writers exclude each other in reality
     (an exec failure above the content writer) is compatible through a
     completion that a later SILENT commit refutes.  Read at the silent
     completion, a silent commit changes nothing, and every commit that
     does change the vector is one writer's. *)
  Definition runS (RUN : (W -> bytes) -> Prop) (md : W -> option bytes) : Prop :=
    exists src, RUN src /\ forall w, src w = default [] (md w).

  Lemma compatN_of_runS RUN md : runS RUN md -> compatN RUN md.
  Proof using.
    intros (src & Hr & Hag). exists src. split; [exact Hr |].
    intros w s Hs. rewrite Hag, Hs. reflexivity.
  Qed.

  Lemma runS_ext RUN md md' :
    (forall w, default [] (md' w) = default [] (md w)) -> runS RUN md -> runS RUN md'.
  Proof using.
    intros Hx (src & Hr & Hag). exists src. split; [exact Hr |]. intros w. rewrite Hag, Hx.
    reflexivity.
  Qed.

  (* a COMMITTED writer: it has written, or fixed the empty source *)
  Definition cmtN (md : W -> option bytes) (sel : list W) (w : W) : bool :=
    bool_decide (w ∈ sel \/ md w = Some []).

  (* the committed sources *)
  Definition rmd (md : W -> option bytes) (sel : list W) : W -> option bytes :=
    fun w => if cmtN md sel w then md w else None.

  (* THE BLOCKS OF A RUN: a merge of every writer's whole source *)
  Definition blkN (ws : list W) (RUN : (W -> bytes) -> Prop) (b : bytes) : Prop :=
    exists src, RUN src /\ merge_all (src <$> ws) b.

  (* a writer that has written has fired *)
  Definition sel_firedN (md : W -> option bytes) (sel : list W) : Prop :=
    forall w, w ∈ sel -> is_Some (md w).

  Lemma compatN_fire RUN md w s :
    compatN RUN (fun w' => if decide (w' = w) then Some s else md w') ->
    compatN RUN md \/ md w <> None.
  Proof using.
    intros (src & Hr & Hag). destruct (md w) eqn:Hmw; [right; congruence |]. left.
    exists src. split; [exact Hr |]. intros w' s' Hm. apply Hag.
    case_decide as Hq; [subst w'; congruence | exact Hm].
  Qed.

  (* THE GENERALISATION OF [PipeBoth.pblk2_wit]: a partial block whose
     fired sources are compatible is a prefix of a block of the model *)
  Lemma pendN_complete (ws : list W) (RUN : (W -> bytes) -> Prop)
      (md : W -> option bytes) (sel : list W) :
    NoDup ws -> (forall x, x ∈ sel -> x ∈ ws) -> sel_firedN md sel ->
    sel_wfN (srcN md) sel -> compatN RUN md ->
    exists b, blkN ws RUN b /\ pendN md sel `prefix_of` b.
  Proof using.
    intros Hnd Hin Hfd Hwf (src & Hr & Hag).
    assert (Heq : forall w, w ∈ sel -> srcN md w = src w).
    { intros w Hw. destruct (Hfd w Hw) as [s Hs]. unfold srcN. rewrite Hs. cbn.
      symmetry. exact (Hag w s Hs). }
    assert (Hwf' : sel_wfN src sel).
    { intros w. destruct (decide (w ∈ sel)) as [Hw | Hw].
      - rewrite <- (Heq w Hw). apply Hwf.
      - rewrite (cntN_nil_notin sel w Hw). lia. }
    destruct (mergeN_complete ws src sel Hnd Hin Hwf') as (b & Hm & Hp).
    exists b. split; [exists src; split; [exact Hr | exact Hm] |].
    unfold pendN. rewrite (mergeN_local (srcN md) src sel Heq). exact Hp.
  Qed.

  (* ...AND AT THE PROMPT: every writer fired and exhausted, the block IS
     one of the model's *)
  Lemma pendN_file (ws : list W) (RUN : (W -> bytes) -> Prop)
      (md : W -> option bytes) (sel : list W) :
    NoDup ws -> (forall x, x ∈ sel -> x ∈ ws) ->
    (forall w, w ∈ ws -> exists s, md w = Some s /\ cntN sel w = length s) ->
    compatN RUN md ->
    blkN ws RUN (pendN md sel).
  Proof using.
    intros Hnd Hin Hall (src & Hr & Hag). exists src. split; [exact Hr |].
    assert (Hmap : src <$> ws = srcN md <$> ws).
    { apply list_fmap_ext. intros i w Hi.
      destruct (Hall w (elem_of_list_lookup_2 _ _ _ Hi)) as (s & Hs & _).
      unfold srcN. rewrite Hs. cbn. exact (Hag w s Hs). }
    rewrite Hmap. unfold pendN. apply mergeN_merge_all; [exact Hnd | exact Hin |].
    intros w Hw. destruct (Hall w Hw) as (s & Hs & Hc). unfold srcN. rewrite Hs. exact Hc.
  Qed.

  (* ---- the fired map, updated at a fire ---- *)
  Definition mdupd (md : W -> option bytes) (w : W) (s : bytes) : W -> option bytes :=
    fun w' => if decide (w' = w) then Some s else md w'.

  Lemma srcN_mdupd_other md w s w' : w' <> w -> srcN (mdupd md w s) w' = srcN md w'.
  Proof using. intros Hne. unfold srcN, mdupd. by rewrite decide_False. Qed.

  Lemma srcN_mdupd_self md w s : srcN (mdupd md w s) w = s.
  Proof using. unfold srcN, mdupd. by rewrite decide_True. Qed.

  (* A FIRE MOVES NOTHING WRITTEN: the fired writer had not written *)
  Lemma pendN_mdupd md sel w s :
    w ∉ sel -> pendN (mdupd md w s) sel = pendN md sel.
  Proof using.
    intros Hw. unfold pendN. apply mergeN_local. intros w' Hw'.
    apply srcN_mdupd_other. intros ->. exact (Hw Hw').
  Qed.

  Lemma sel_wfN_mdupd md sel w s :
    w ∉ sel -> sel_wfN (srcN md) sel -> sel_wfN (srcN (mdupd md w s)) sel.
  Proof using.
    intros Hw Hwf w'. destruct (decide (w' = w)) as [-> | Hne].
    - rewrite (cntN_nil_notin sel w Hw). lia.
    - rewrite srcN_mdupd_other by exact Hne. apply Hwf.
  Qed.

  Lemma sel_firedN_mdupd md sel w s :
    sel_firedN md sel -> sel_firedN (mdupd md w s) sel.
  Proof using.
    intros Hf w' Hw'. unfold mdupd. case_decide; [by eexists | exact (Hf w' Hw')].
  Qed.

  Lemma sel_firedN_snoc md sel w :
    sel_firedN md sel -> is_Some (md w) -> sel_firedN md (sel ++ [w]).
  Proof using.
    intros Hf Hw w' Hw'. apply elem_of_app in Hw' as [Hw' | Hw']; [exact (Hf w' Hw') |].
    apply elem_of_list_singleton in Hw' as ->. exact Hw.
  Qed.

  (* THE BYTE STEP, at the fired sources *)
  Lemma pendN_snoc md sel w s b :
    sel_wfN (srcN md) sel -> md w = Some s -> s !! cntN sel w = Some b ->
    pendN md (sel ++ [w]) = pendN md sel ++ [b].
  Proof using.
    intros Hwf Hs Hb. unfold pendN. apply (mergeN_snoc _ sel w b Hwf).
    unfold srcN. rewrite Hs. exact Hb.
  Qed.

  Lemma sel_wfN_fired_snoc md sel w s :
    sel_wfN (srcN md) sel -> md w = Some s -> cntN sel w < length s ->
    sel_wfN (srcN md) (sel ++ [w]).
  Proof using.
    intros Hwf Hs Hlt. apply sel_wfN_snoc; [exact Hwf |]. unfold srcN. rewrite Hs. exact Hlt.
  Qed.
End mergeN.

(* ===================================================================== *)
(*  4.  THE PIPELINE'S WRITERS                                            *)
(* ===================================================================== *)

(* sh node [k] (sigma_k: its [pipe] or [fork] panic), the left stage [k]
   (lambda_k: the producer at [k = 0], a middle cat after), and the last
   cat (rho) *)
Inductive wid := WSh (k : nat) | WLeft (k : nat) | WLast.

Global Instance wid_eq_dec : EqDecision wid.
Proof using. solve_decision. Defined.

(* the writers of a pipeline of [n] cats below the producer, from sh node
   [k] down: sigma_k, lambda_k, sigma_(k+1), .., rho *)
Fixpoint wids_from (k n : nat) : list wid :=
  match n with
  | 0 => [WLast]
  | S n' => WSh k :: WLeft k :: wids_from (S k) n'
  end.

Definition wids (n : nat) : list wid := wids_from 0 n.

Lemma wids_from_in k n w :
  w ∈ wids_from k n ->
  match w with WSh j | WLeft j => k <= j | WLast => True end.
Proof using.
  revert k. induction n as [| n IH]; intros k Hw; cbn [wids_from] in Hw.
  - apply elem_of_list_singleton in Hw as ->. exact I.
  - apply elem_of_cons in Hw as [-> | Hw]; [lia |].
    apply elem_of_cons in Hw as [-> | Hw]; [lia |].
    specialize (IH (S k) Hw). destruct w; lia || exact I.
Qed.

Lemma wids_from_NoDup k n : NoDup (wids_from k n).
Proof using.
  revert k. induction n as [| n IH]; intros k; cbn [wids_from].
  - apply NoDup_singleton.
  - apply NoDup_cons. split.
    + intros Hw. apply elem_of_cons in Hw as [Hw | Hw]; [discriminate Hw |].
      pose proof (wids_from_in (S k) n (WSh k) Hw) as H. cbn in H. lia.
    + apply NoDup_cons. split; [| apply IH].
      intros Hw. pose proof (wids_from_in (S k) n (WLeft k) Hw) as H. cbn in H. lia.
Qed.

Lemma wids_NoDup n : NoDup (wids n).
Proof using. apply wids_from_NoDup. Qed.

Lemma wids_from_length k n : length (wids_from k n) = 2 * n + 1.
Proof using. revert k. induction n as [| n IH]; intros k; cbn [wids_from length]; [lia | rewrite IH; lia]. Qed.

(* the number of filter stages of a line (an echo line has the one
   writer, rho, which is then the echo process itself) *)
Definition lcats (l : pline') : nat :=
  match l with LEcho' _ => 0 | LPipes _ fs => length fs end.

Lemma lcats_cats (p : producer) (n : nat) : lcats (LPipes p (cats n)) = n.
Proof using. exact (FileDisc.cats_length n). Qed.

(* the filter stages of a line, and the one that writes pipe [j] (pipe 0
   is the producer's, which is no filter's: [FCat] there is inert) *)
Definition lfilts (l : pline') : list filt :=
  match l with LEcho' _ => [] | LPipes _ fs => fs end.
Definition lfilt (l : pline') (j : nat) : filt := nth (j - 1) (lfilts l) FCat.

Lemma lcats_lfilts (l : pline') : lcats l = length (lfilts l).
Proof using. by destruct l. Qed.

Lemma nth_cats (n i : nat) : nth i (cats n) FCat = FCat.
Proof using. unfold FileDisc.cats. revert i. induction n as [| n IH]; intros [| i]; cbn; auto. Qed.

Lemma lfilt_cats (p : producer) (n j : nat) : lfilt (LPipes p (cats n)) j = FCat.
Proof using. exact (nth_cats n (j - 1)). Qed.

(* ---- THE PER-WRITER RUNS: [PipesDisc.sfx_run] / [line_run] with the
       silent writers' streams in place, in [wids] order, over the line's
       filter stages (cut G5; at [cats n] they are the all-cat runs the
       round is exercised at) ---- *)

Inductive sfx_runV (fc : bytes -> option bytes) (L : bytes)
    : list filt -> wr_out -> bool -> list bytes -> Prop :=
  | srv_last F win wc so :
      stage_out fc L (SLast F) so -> pipe_pairB L wc win (rd_of so) ->
      sfx_runV fc L [F] win wc [so_cons so]
  | srv_pipe_fail F F' fs win wc :
      sfx_runV fc L (F :: F' :: fs) win wc (dg_pipe_b :: replicate (2 * length (F' :: fs)) [])
  | srv_node F F' fs win wc so vs :
      stage_out fc L (SMid F) so -> pipe_pairB L wc win (rd_of so) ->
      sfx_runV fc L (F' :: fs) (wr_of so) (filt_is_cat F) vs ->
      sfx_runV fc L (F :: F' :: fs) win wc ([] :: so_cons so :: vs).

Inductive line_runV (fc : bytes -> option bytes) : pline' -> list bytes -> Prop :=
  | lrv_echo ws : line_runV fc (LEcho' ws) [wl_line (drop 1 ws)]
  | lrv_echo_exec ws : line_runV fc (LEcho' ws) [dg_execL]
  | lrv_echo_silent ws : line_runV fc (LEcho' ws) [[]]
  | lrv_pipe_fail p fs : fs <> [] -> line_runV fc (LPipes p fs) (dg_pipe_b :: replicate (2 * length fs) [])
  | lrv_node p fs so vs :
      stage_out fc (prod_content fc p) (SProd p) so ->
      sfx_runV fc (prod_content fc p) fs (wr_of so) (prod_cat p) vs ->
      line_runV fc (LPipes p fs) ([] :: so_cons so :: vs).

Lemma lcats_pos (p : producer) (fs : list filt) : fs <> [] -> 1 <= lcats (LPipes p fs).
Proof using. destruct fs as [| F fs]; [intros H; exfalso; exact (H eq_refl) | cbn; lia]. Qed.

(* an all-cat line, restated at its own count (the node's [Hline]) *)
Lemma lpipes_cats_eq (p : producer) (n : nat) :
  LPipes p (cats n) = LPipes p (cats (lcats (LPipes p (cats n)))).
Proof using. rewrite lcats_cats. reflexivity. Qed.

(* THE COMPLETE RUNS, as source vectors *)
Definition runN (fc : bytes -> option bytes) (l : pline') (src : wid -> bytes) : Prop :=
  line_runV fc l (src <$> wids (lcats l)).

(* ---- dropping the silent writers ---- *)

(* [vs] is [ss] with empty streams inserted *)
Inductive nil_ext : list bytes -> list bytes -> Prop :=
  | ne_nil : nil_ext [] []
  | ne_keep x ss vs : nil_ext ss vs -> nil_ext (x :: ss) (x :: vs)
  | ne_drop ss vs : nil_ext ss vs -> nil_ext ss ([] :: vs).

Lemma nil_ext_rep k : nil_ext [] (replicate k []).
Proof using. induction k as [| k IH]; [constructor | apply ne_drop, IH]. Qed.

Lemma nil_ext_forall ss vs :
  nil_ext ss vs -> Forall (fun s => s = []) vs -> Forall (fun s => s = []) ss.
Proof using.
  induction 1 as [| x ss vs H IH | ss vs H IH]; intros HF; [constructor | |].
  - apply Forall_cons_1 in HF as [Hx HF]. constructor; [exact Hx | exact (IH HF)].
  - apply Forall_cons_1 in HF as [_ HF]. exact (IH HF).
Qed.

Lemma nil_ext_take ss vs i x s :
  nil_ext ss vs -> vs !! i = Some (x :: s) ->
  exists i', ss !! i' = Some (x :: s) /\ nil_ext (<[i' := s]> ss) (<[i := s]> vs).
Proof using.
  intros H. revert i. induction H as [| y ss vs H IH | ss vs H IH]; intros i Hi.
  - discriminate Hi.
  - destruct i as [| j]; cbn in Hi.
    + injection Hi as ->. exists 0. split; [reflexivity |]. cbn. constructor. exact H.
    + destruct (IH j Hi) as (i' & Hi' & Hne). exists (S i'). split; [exact Hi' |].
      cbn. constructor. exact Hne.
  - destruct i as [| j]; cbn in Hi; [discriminate Hi |].
    destruct (IH j Hi) as (i' & Hi' & Hne). exists i'. split; [exact Hi' |].
    cbn. constructor. exact Hne.
Qed.

(* A MERGE WITH THE SILENT WRITERS IS A MERGE WITHOUT THEM *)
Lemma merge_all_nil_ext vs b : merge_all vs b -> forall ss, nil_ext ss vs -> merge_all ss b.
Proof using.
  induction 1 as [vs HF | vs i x s b Hi Hm IH]; intros ss Hne.
  - apply ma_done. exact (nil_ext_forall ss vs Hne HF).
  - destruct (nil_ext_take ss vs i x s Hne Hi) as (i' & Hi' & Hne').
    apply (ma_take _ i' x s); [exact Hi' | exact (IH _ Hne')].
Qed.

Lemma sfx_runV_run fc L fs win wc vs :
  sfx_runV fc L fs win wc vs -> exists ss, sfx_run fc L fs win wc ss /\ nil_ext ss vs.
Proof using.
  induction 1 as [F win wc so Hso Hp | F F' fs win wc
                 | F F' fs win wc so vs Hso Hp Hr (ss & Hss & Hne)].
  - exists [so_cons so]. split; [exact (sr_last fc L F win wc so Hso Hp) |].
    constructor. constructor.
  - exists [dg_pipe_b]. split; [apply sr_pipe_fail |]. constructor. apply nil_ext_rep.
  - exists (so_cons so :: ss).
    split; [exact (sr_node fc L F F' fs win wc so ss Hso Hp Hss) |].
    apply ne_drop. constructor. exact Hne.
Qed.

Lemma line_runV_run fc l vs :
  line_runV fc l vs -> exists ss, line_run fc l ss /\ nil_ext ss vs.
Proof using.
  destruct 1 as [ws | ws | ws | p fs Hn | p fs so vs Hso Hr].
  - exists [wl_line (drop 1 ws)]. split; [apply lr_echo | repeat constructor].
  - exists [dg_execL]. split; [apply lr_echo_exec | repeat constructor].
  - exists [[]]. split; [apply lr_echo_silent | repeat constructor].
  - exists [dg_pipe_b]. split; [exact (lr_pipe_fail fc p fs Hn) |].
    constructor. apply nil_ext_rep.
  - destruct (sfx_runV_run _ _ _ _ _ _ Hr) as (ss & Hss & Hne).
    exists (so_cons so :: ss). split; [exact (lr_node fc p fs so ss Hso Hss) |].
    apply ne_drop. constructor. exact Hne.
Qed.

(* THE BRIDGE: a block of a per-writer run is one of [PipesDisc]'s *)
Lemma line_runV_blocks fc l vs b :
  line_runV fc l vs -> merge_all vs b -> line_blocks fc l b.
Proof using.
  intros Hr Hm. destruct (line_runV_run fc l vs Hr) as (ss & Hss & Hne).
  exists ss. split; [exact Hss | exact (merge_all_nil_ext vs b Hm ss Hne)].
Qed.

Lemma blkN_line_blocks fc l b :
  blkN (wids (lcats l)) (runN fc l) b -> line_blocks fc l b.
Proof using. intros (src & Hr & Hm). exact (line_runV_blocks fc l _ b Hr Hm). Qed.

(* ===================================================================== *)
(*  5.  THE ADMISSIBLE ALTERNATIVE A PARTIAL BLOCK IS A PREFIX OF         *)
(* ===================================================================== *)

(* WHAT THE CLAIM'S OPEN ROUND READS (the analogue of
   [PipeBoth.pblk2_wit] at the line model): an admitted alternative of the
   line that neither panics nor ends coverage, whose continuation the
   block so far is a prefix of *)
Definition pipesN_wit (fc : bytes -> option bytes) (adm : pline' -> bool)
    (l : pline') (pre : bytes) : Prop :=
  exists a : plalt,
    lm_ok (pipes_lm fc adm) tt l a
    /\ lm_panic (pipes_lm fc adm) a = false
    /\ lm_term (pipes_lm fc adm) a = false
    /\ pre `prefix_of` lm_cont (pipes_lm fc adm) tt l a.

Lemma pipesN_wit_of_blk fc adm l pre b :
  adm l = true -> blkN (wids (lcats l)) (runN fc l) b -> pre `prefix_of` b ->
  pipesN_wit fc adm l pre.
Proof using.
  intros Ha Hb Hp. exists (PLRun b). cbn [pipes_lm lm_ok lm_panic lm_term lm_cont plpanic plterm plcont].
  split; [right; split; [exact Ha | exact (blkN_line_blocks fc l b Hb)] |].
  split; [reflexivity | split; [reflexivity |]].
  etrans; [exact Hp |]. by eexists.
Qed.

(* THE LEMMA OF THE CUT: a partial block with every writer's source fixed
   compatibly completes to an admissible block of the model *)
Theorem pipesN_complete fc adm l (md : wid -> option bytes) (sel : list wid) :
  adm l = true ->
  (forall x, x ∈ sel -> x ∈ wids (lcats l)) -> sel_firedN md sel ->
  sel_wfN (srcN md) sel -> compatN (runN fc l) md ->
  pipesN_wit fc adm l (pendN md sel).
Proof using.
  intros Ha Hin Hfd Hwf Hc.
  destruct (pendN_complete (wids (lcats l)) (runN fc l) md sel (wids_NoDup _) Hin Hfd Hwf Hc)
    as (b & Hb & Hp).
  exact (pipesN_wit_of_blk fc adm l _ b Ha Hb Hp).
Qed.

(* ...and every block of the model is '$'-free, so the open round's block
   is too (the claim's non-terminal reading asks for it) -- at every
   admission ([PipesDisc.pipes_block_nodollar]) *)
Lemma pipesN_blk_nodollar fc l b :
  fc_ok fc -> pl_ok l -> blkN (wids (lcats l)) (runN fc l) b -> Forall nodollar b.
Proof using.
  intros Hfc Hl Hb. exact (pipes_block_nodollar fc l b Hfc Hl (blkN_line_blocks fc l b Hb)).
Qed.

(* ...and at a well-formed line the partial block is '$'-free, which is
   what the claim's non-terminal open reading asks beside the witness *)
Theorem pipesN_complete_nd fc adm l (md : wid -> option bytes) (sel : list wid) :
  fc_ok fc -> adm l = true -> pl_ok l ->
  (forall x, x ∈ sel -> x ∈ wids (lcats l)) -> sel_firedN md sel ->
  sel_wfN (srcN md) sel -> compatN (runN fc l) md ->
  pipesN_wit fc adm l (pendN md sel) /\ Forall nodollar (pendN md sel).
Proof using.
  intros Hfc Ha Hl Hin Hfd Hwf Hc.
  destruct (pendN_complete (wids (lcats l)) (runN fc l) md sel (wids_NoDup _) Hin Hfd Hwf Hc)
    as (b & Hb & Hp).
  split; [exact (pipesN_wit_of_blk fc adm l _ b Ha Hb Hp) |].
  exact (prefix_forall _ _ _ Hp (pipesN_blk_nodollar fc l b Hfc Hl Hb)).
Qed.

(* ===================================================================== *)
(*  6.  THE TERMINAL ROUNDS, WRITER BY WRITER (cut C5b)                   *)
(*                                                                        *)
(*  [PipesDisc.line_term] read per writer, as [line_runV] reads           *)
(*  [line_run]: at a fork failure of sh node k, sigma_k's source is its   *)
(*  [fork] line and then -- one process later, at the same cursor -- the  *)
(*  main loop's prompt ([PipeDisc.alt_forkc], the landed convention); the *)
(*  stages above it (lambda_0 .. lambda_(k-1)) were waited, lambda_k is   *)
(*  the STRAY, and everything below node k never ran.                     *)
(*                                                                        *)
(*  A block of such a round is a merge by writer index whose PROMPT BYTES *)
(*  come after every waited stage is exhausted ([prompt_ok_src]); the     *)
(*  merge is then a prefix of a terminal block of the model               *)
(*  ([termN_blocks]) -- at EVERY such selector, the landed                *)
(*  [PipeBoth.pblk2_wit_t_forkc]'s shape.  The family's terminal          *)
(*  invariant [tokN] is the committed sources' compatibility with a       *)
(*  terminal vector and that ordering, read at the fired sources.         *)
(* ===================================================================== *)

Section mergeN_term.
  Context {W : Type} `{!EqDecision W}.

  (* a byte of the terminal writer [T] past what is left of its fork line
     [fr] comes after every waited writer of [Wd] has written its whole
     source *)
  Definition prompt_ok_src (Wd : list W) (T : W) (fr : bytes) (src : W -> bytes)
      (sel : list W) : Prop :=
    forall s1 s2, sel = s1 ++ T :: s2 -> length fr <= cntN s1 T ->
      forall w, w ∈ Wd -> cntN s1 w = length (src w).

  Lemma fmap_supd_notin (src : W -> bytes) (Wd : list W) (w : W) (r : bytes) :
    w ∉ Wd -> supd src w r <$> Wd = src <$> Wd.
  Proof using.
    intros Hw. apply list_fmap_ext. intros i x Hx. unfold supd.
    rewrite decide_False; [reflexivity |]. intros ->. apply Hw.
    exact (elem_of_list_lookup_2 _ _ _ Hx).
  Qed.

  Lemma insert_last {A} (l : list A) (y x : A) : <[length l := x]> (l ++ [y]) = l ++ [x].
  Proof using. pose proof (insert_app_r l [y] 0 x) as H. rewrite Nat.add_0_r in H. exact H. Qed.

  (* THE FORWARD WALK: the merge, read byte by byte from the front, is
     accepted by the prefix test of a terminal block *)
  Lemma mergeN_ptermb (Wd : list W) (T S : W) :
    NoDup Wd -> T ∉ Wd -> S ∉ Wd -> T <> S ->
    forall sel src fr pr,
      src T = fr ++ pr ->
      (forall w, w ∈ sel -> w = T \/ w = S \/ w ∈ Wd) ->
      sel_wfN src sel ->
      prompt_ok_src Wd T fr src sel ->
      ptermb ((src <$> Wd) ++ [fr]) pr (src S) (mergeN src sel) = true.
  Proof using.
    intros Hnd HT HS HTS sel. induction sel as [| w s IH]; intros src fr pr HsT Hin Hwf Hpo.
    - reflexivity.
    - destruct (sel_wfN_cons_inv src w s Hwf) as (y & r & Hs & Hwf').
      cbn [mergeN]. rewrite Hs. cbn [ptermb]. rewrite !orb_true_iff.
      assert (HIN : forall x, x ∈ s -> x = T \/ x = S \/ x ∈ Wd)
        by (intros x Hx; apply Hin; by apply elem_of_list_further).
      (* the step's reading of the split before the rest *)
      assert (Hpo1 : forall s1 s2, s = s1 ++ T :: s2 ->
                       length fr <= cntN (w :: s1) T ->
                       forall x, x ∈ Wd -> cntN (w :: s1) x = length (src x)).
      { intros s1 s2 Heq. apply (Hpo (w :: s1) s2). rewrite Heq. reflexivity. }
      destruct (Hin w (elem_of_list_here w s)) as [-> | [-> | Hw]].
      + (* THE TERMINAL WRITER: its fork line, or the prompt *)
        rewrite HsT in Hs.
        assert (HmS : supd src T r S = src S)
          by (unfold supd; rewrite decide_False; [reflexivity | congruence]).
        assert (HmW : supd src T r <$> Wd = src <$> Wd) by exact (fmap_supd_notin src Wd T r HT).
        assert (Hcnt : forall s1 x, x ∈ Wd -> cntN (T :: s1) x = cntN s1 x).
        { intros s1 x Hx. cbn [cntN]. rewrite decide_False; [lia | intros ->; exact (HT Hx)]. }
        assert (HmX : forall x, x ∈ Wd -> supd src T r x = src x).
        { intros x Hx. unfold supd. rewrite decide_False; [reflexivity | intros ->; exact (HT Hx)]. }
        destruct fr as [| f0 fr'].
        * (* the prompt: every waited writer is done *)
          cbn [app] in Hs. subst pr. left. right. apply andb_true_iff. split.
          -- apply forallb_nil_iff. apply Forall_app. split; [| by apply Forall_singleton].
             apply Forall_forall. intros z Hz. apply elem_of_list_fmap in Hz as (x & -> & Hx).
             pose proof (Hpo [] s eq_refl ltac:(cbn [length]; lia) x Hx) as Hc.
             cbn [cntN] in Hc. symmetry in Hc. by apply nil_length_inv.
          -- change (bool_decide (y = y) && ptermb ((src <$> Wd) ++ [[]]) r
                       (src S) (mergeN (supd src T r) s) = true).
             rewrite bool_decide_eq_true_2; [| reflexivity]. cbn [andb].
             assert (Hrec : ptermb ((supd src T r <$> Wd) ++ [[]]) r (supd src T r S)
                              (mergeN (supd src T r) s) = true).
             { apply IH; [unfold supd; by rewrite decide_True | exact HIN | exact Hwf' |].
               intros s1 s2 Heq _ x Hx.
               assert (Hle : length (@nil (bv 8)) <= cntN (T :: s1) T) by (cbn [length]; lia).
               pose proof (Hpo1 s1 s2 Heq Hle x Hx) as Hc.
               rewrite (Hcnt s1 x Hx) in Hc. rewrite (HmX x Hx). exact Hc. }
             rewrite HmS, HmW in Hrec. exact Hrec.
        * (* a byte of the fork line: the last waited stream *)
          cbn [app] in Hs. injection Hs as <- Hr.
          assert (Hrec : ptermb ((supd src T r <$> Wd) ++ [fr']) pr (supd src T r S)
                           (mergeN (supd src T r) s) = true).
          { apply IH; [unfold supd; rewrite decide_True; [exact (eq_sym Hr) | reflexivity]
                      | exact HIN | exact Hwf' |].
            intros s1 s2 Heq Hle x Hx.
            assert (Hle' : length (f0 :: fr') <= cntN (T :: s1) T).
            { cbn [cntN length]. rewrite decide_True; [lia | reflexivity]. }
            pose proof (Hpo1 s1 s2 Heq Hle' x Hx) as Hc.
            rewrite (Hcnt s1 x Hx) in Hc. rewrite (HmX x Hx). exact Hc. }
          rewrite HmS, HmW in Hrec.
          left. left. apply existsb_exists.
          exists ((src <$> Wd) ++ [fr']). split; [| exact Hrec].
          apply elem_of_list_In, picks_spec. exists (length (src <$> Wd)), fr'.
          split; [apply list_lookup_middle; reflexivity |].
          symmetry. apply insert_last.
      + (* THE STRAY *)
        right. rewrite Hs.
        change (bool_decide (y = y) && ptermb ((src <$> Wd) ++ [fr]) pr r
                  (mergeN (supd src S r) s) = true).
        rewrite bool_decide_eq_true_2; [| reflexivity]. cbn [andb].
        assert (HmT : supd src S r T = src T)
          by (unfold supd; rewrite decide_False; [reflexivity | congruence]).
        assert (HmS : supd src S r S = r) by (unfold supd; by rewrite decide_True).
        assert (HmW : supd src S r <$> Wd = src <$> Wd) by exact (fmap_supd_notin src Wd S r HS).
        assert (Hrec : ptermb ((supd src S r <$> Wd) ++ [fr]) pr (supd src S r S)
                         (mergeN (supd src S r) s) = true).
        { apply IH; [rewrite HmT; exact HsT | exact HIN | exact Hwf' |].
          intros s1 s2 Heq Hle x Hx.
          assert (Hle' : length fr <= cntN (S :: s1) T).
          { cbn [cntN]. rewrite decide_False; [lia | congruence]. }
          pose proof (Hpo1 s1 s2 Heq Hle' x Hx) as Hc.
          cbn [cntN] in Hc. rewrite decide_False in Hc; [| intros ->; exact (HS Hx)].
          unfold supd. rewrite decide_False; [exact Hc | intros ->; exact (HS Hx)]. }
        rewrite HmS, HmW in Hrec. exact Hrec.
      + (* A WAITED WRITER *)
        assert (HwT : w <> T) by (intros ->; exact (HT Hw)).
        assert (HwS : w <> S) by (intros ->; exact (HS Hw)).
        destruct (elem_of_list_lookup_1 Wd w Hw) as (i & Hi).
        assert (Hlen : i < length (src <$> Wd))
          by (rewrite length_fmap; exact (lookup_lt_Some _ _ _ Hi)).
        assert (HmS : supd src w r S = src S)
          by (unfold supd; rewrite decide_False; [reflexivity | congruence]).
        assert (Hrec : ptermb ((supd src w r <$> Wd) ++ [fr]) pr (supd src w r S)
                         (mergeN (supd src w r) s) = true).
        { apply IH; [unfold supd; rewrite decide_False; [exact HsT | congruence]
                    | exact HIN | exact Hwf' |].
          intros s1 s2 Heq Hle x Hx.
          assert (Hle' : length fr <= cntN (w :: s1) T).
          { cbn [cntN]. rewrite decide_False; [lia | congruence]. }
          pose proof (Hpo1 s1 s2 Heq Hle' x Hx) as Hc.
          cbn [cntN] in Hc. unfold supd. destruct (decide (x = w)) as [-> | Hne].
          - rewrite decide_True in Hc; [| reflexivity]. rewrite Hs in Hc.
            cbn [length] in Hc. lia.
          - rewrite decide_False in Hc; [lia | congruence]. }
        rewrite HmS in Hrec.
        left. left. apply existsb_exists.
        exists ((supd src w r <$> Wd) ++ [fr]). split; [| exact Hrec].
        apply elem_of_list_In, picks_spec. exists i, r. split.
        * rewrite lookup_app_l; [| exact Hlen]. rewrite list_lookup_fmap, Hi. cbn.
          rewrite Hs. reflexivity.
        * rewrite insert_app_l; [| exact Hlen]. f_equal. symmetry.
          exact (map_supd_insert src Wd i w r Hnd Hi).
  Qed.

  (* ...AND THE MERGE IS A PREFIX OF A SHUFFLE of (the waited streams and
     the fork line, merged, then the prompt) with a prefix of the stray *)
  Lemma mergeN_term_prefix (Wd : list W) (T S : W) (src : W -> bytes) (f pr : bytes)
      (sel : list W) :
    NoDup Wd -> T ∉ Wd -> S ∉ Wd -> T <> S ->
    src T = f ++ pr ->
    (forall w, w ∈ sel -> w = T \/ w = S \/ w ∈ Wd) ->
    sel_wfN src sel -> prompt_ok_src Wd T f src sel ->
    exists Wm sp b', merge_all ((src <$> Wd) ++ [f]) Wm /\ sp `prefix_of` src S
                     /\ merge_all [Wm ++ pr; sp] b' /\ mergeN src sel `prefix_of` b'.
  Proof using.
    intros Hnd HT HS HTS HsT Hin Hwf Hpo. apply ptermb_spec.
    exact (mergeN_ptermb Wd T S Hnd HT HS HTS sel src f pr HsT Hin Hwf Hpo).
  Qed.
End mergeN_term.

(* ---- the pipeline's terminal vectors ---- *)

Local Instance WLeft_inj : Inj (=) (=) WLeft.
Proof using. intros x y H. by injection H. Qed.

(* the stages above node k: waited *)
Definition waitedN (k : nat) : list wid := WLeft <$> seq 0 k.

Lemma waitedN_elem k w : w ∈ waitedN k <-> exists j, w = WLeft j /\ j < k.
Proof using.
  unfold waitedN. rewrite elem_of_list_fmap. split.
  - intros (j & -> & Hj). apply elem_of_seq in Hj. exists j. split; [reflexivity | lia].
  - intros (j & -> & Hj). exists j. split; [reflexivity |]. apply elem_of_seq. lia.
Qed.

Lemma waitedN_NoDup k : NoDup (waitedN k).
Proof using. unfold waitedN. apply NoDup_fmap_2; [apply _ | apply NoDup_seq]. Qed.

(* THE TERMINAL VECTOR AT NODE [k]: [line_term] read writer by writer *)
Definition termN (fc : bytes -> option bytes) (l : pline') (k : nat) (src : wid -> bytes)
    : Prop :=
  k < lcats l
  /\ src (WSh k) = alt_forkc
  /\ (forall j, j <> k -> src (WSh j) = [])
  /\ (forall j, k < j -> src (WLeft j) = [])
  /\ src WLast = []
  /\ line_term fc l ((src <$> waitedN k) ++ [dg_fork_b]) (src (WLeft k)).

Definition termsN (fc : bytes -> option bytes) (l : pline') (src : wid -> bytes) : Prop :=
  exists k, termN fc l k src.

Lemma alt_forkc_fork : alt_forkc = dg_fork_b ++ u_prompt.
Proof using. reflexivity. Qed.

Lemma dg_fork_b_len : length dg_fork_b = 5.
Proof using. vm_compute. reflexivity. Qed.

(* THE FAMILY-LEVEL WITNESS: every well-formed selector over a terminal
   vector whose prompt bytes follow the waited stages is a prefix of a
   terminal block of the model *)
Theorem termN_blocks fc l k src (sel : list wid) :
  termN fc l k src ->
  sel_wfN src sel ->
  prompt_ok_src (waitedN k) (WSh k) dg_fork_b src sel ->
  exists b', line_term_blocks fc l b' /\ mergeN src sel `prefix_of` b'.
Proof using.
  intros (Hk & HT & HshO & HlfO & Hlast & Hlt) Hwf Hpo.
  assert (Hin : forall w, w ∈ sel -> w = WSh k \/ w = WLeft k \/ w ∈ waitedN k).
  { intros w Hw. assert (Hne : src w <> []).
    { intros Hq. pose proof (Hwf w) as Hc. rewrite Hq in Hc. cbn [length] in Hc.
      apply cntN_elem in Hw. lia. }
    destruct w as [j | j |].
    - left. destruct (decide (j = k)) as [-> | Hjk]; [reflexivity |].
      by destruct (Hne (HshO j Hjk)).
    - destruct (decide (j = k)) as [-> | Hjk]; [right; left; reflexivity |].
      right. right. apply waitedN_elem. exists j. split; [reflexivity |].
      destruct (decide (k < j)) as [Hkj | Hkj]; [by destruct (Hne (HlfO j Hkj)) | lia].
    - by destruct (Hne Hlast). }
  destruct (mergeN_term_prefix (waitedN k) (WSh k) (WLeft k) src dg_fork_b u_prompt sel
              (waitedN_NoDup k)
              ltac:(intros Hq; apply waitedN_elem in Hq as (j & Hq & _); discriminate Hq)
              ltac:(intros Hq; apply waitedN_elem in Hq as (j & Hq & Hj); injection Hq as ->; lia)
              ltac:(discriminate) HT Hin Hwf Hpo)
    as (Wm & sp & b' & HWm & Hsp & Hm & Hp).
  exists b'. split; [| exact Hp].
  exists ((src <$> waitedN k) ++ [dg_fork_b]), (src (WLeft k)), Wm, sp. split_and!; assumption.
Qed.

(* ---- THE TERMINAL INVARIANT, at the fired sources ---- *)

(* the terminal writer's prompt bytes follow the waited stages, each of
   which has fixed its source and written all of it *)
Definition prompt_okN (md : wid -> option bytes) (sel : list wid) : Prop :=
  forall s1 s2 k, sel = s1 ++ WSh k :: s2 -> md (WSh k) = Some alt_forkc ->
    length dg_fork_b <= cntN s1 (WSh k) ->
    forall j, j < k -> exists s, md (WLeft j) = Some s /\ cntN s1 (WLeft j) = length s.

(* the COMMITTED sources (written, or the empty source fixed) extend to a
   terminal vector, and the prompt follows the waited stages *)
Definition tokN (fc : bytes -> option bytes) (l : pline') (md : wid -> option bytes)
    (sel : list wid) : Prop :=
  runS (termsN fc l) (rmd md sel) /\ prompt_okN md sel.

(* the committed sources agree with the silent completion *)
(* A SILENT COMMIT leaves the silent completion as it was *)
Lemma rmd_silence_src {W : Type} `{!EqDecision W} (md : W -> option bytes) (sel : list W)
    (w x : W) :
  w ∉ sel -> md w = None ->
  default [] (rmd (mdupd md w []) sel x) = default [] (rmd md sel x).
Proof using.
  intros Hws Hmw. unfold rmd, cmtN, mdupd.
  case_decide as Hxw.
  - subst x.
    rewrite (bool_decide_eq_false_2 (w ∈ sel \/ md w = Some []));
      [| intros [Hin | Hq]; [exact (Hws Hin) | rewrite Hmw in Hq; discriminate Hq]].
    case_bool_decide; reflexivity.
  - reflexivity.
Qed.

Lemma runS_committed (RUN : (wid -> bytes) -> Prop) (md : wid -> option bytes) (sel : list wid) :
  runS RUN (rmd md sel) ->
  exists src, RUN src /\ forall w s, (w ∈ sel \/ md w = Some []) -> md w = Some s -> src w = s.
Proof using.
  intros (src & Hr & Hag). exists src. split; [exact Hr |].
  intros w s Hc Hs. rewrite Hag. unfold rmd, cmtN. rewrite bool_decide_true by exact Hc.
  rewrite Hs. reflexivity.
Qed.

(* THE TERMINAL WITNESS, DERIVED: the block of a family state the
   invariant holds at is a prefix of a terminal block *)
Theorem tokN_blocks fc l (md : wid -> option bytes) (sel : list wid) :
  tokN fc l md sel -> sel_firedN md sel -> sel_wfN (srcN md) sel ->
  exists b', line_term_blocks fc l b' /\ pendN md sel `prefix_of` b'.
Proof using.
  intros (Hrs & Hpo) Hfd Hwf.
  destruct (runS_committed _ md sel Hrs) as (src & (k & Htm) & Hag).
  assert (Heq : forall w, w ∈ sel -> srcN md w = src w).
  { intros w Hw. destruct (Hfd w Hw) as [s Hs]. unfold srcN. rewrite Hs. cbn.
    symmetry. exact (Hag w s (or_introl Hw) Hs). }
  assert (Hwf' : sel_wfN src sel).
  { intros w. destruct (decide (w ∈ sel)) as [Hw | Hw].
    - rewrite <- (Heq w Hw). apply Hwf.
    - rewrite (cntN_nil_notin sel w Hw). lia. }
  assert (Hpo' : prompt_ok_src (waitedN k) (WSh k) dg_fork_b src sel).
  { intros s1 s2 Hsel Hle w Hw. apply waitedN_elem in Hw as (j & -> & Hj).
    assert (HTin : WSh k ∈ sel) by (rewrite Hsel; apply elem_of_app; right; apply elem_of_list_here).
    assert (HmT : md (WSh k) = Some alt_forkc).
    { destruct (Hfd _ HTin) as [s Hs]. rewrite Hs. f_equal.
      rewrite <- (Hag _ s (or_introl HTin) Hs). exact (proj1 (proj2 Htm)). }
    destruct (Hpo s1 s2 k Hsel HmT Hle j Hj) as (s & Hs & Hc).
    rewrite Hc. f_equal. symmetry. apply (Hag _ s); [| exact Hs].
    destruct s as [| x s'] eqn:Hse; [right; exact Hs |]. left.
    rewrite Hsel. apply elem_of_app. left. apply cntN_elem. rewrite Hc. cbn [length]. lia. }
  destruct (termN_blocks fc l k src sel Htm Hwf' Hpo') as (b' & Hb & Hp).
  exists b'. split; [exact Hb |]. unfold pendN. rewrite (mergeN_local (srcN md) src sel Heq).
  exact Hp.
Qed.

(* ---- how the invariant moves ---- *)

Lemma app_cons_eq_snoc {A} (s1 s2 sel : list A) (x w : A) :
  s1 ++ x :: s2 = sel ++ [w] ->
  (s1 = sel /\ x = w /\ s2 = []) \/ exists s2', s2 = s2' ++ [w] /\ sel = s1 ++ x :: s2'.
Proof using.
  intros H. destruct (decide (s2 = [])) as [-> | Hne].
  - left. apply app_inj_tail in H as [-> ->]. done.
  - right. destruct (exists_last Hne) as (s2' & z & ->).
    rewrite app_comm_cons, app_assoc in H. apply app_inj_tail in H as [<- ->].
    exists s2'. split; [reflexivity |]. reflexivity.
Qed.

(* a byte that is not a prompt byte *)
Lemma prompt_okN_snoc md sel w :
  prompt_okN md sel ->
  (forall k, w = WSh k -> md (WSh k) = Some alt_forkc -> cntN sel w < length dg_fork_b) ->
  prompt_okN md (sel ++ [w]).
Proof using.
  intros Hpo Hw s1 s2 k Hsel HmT Hle j Hj.
  destruct (app_cons_eq_snoc s1 s2 sel (WSh k) w (eq_sym Hsel)) as [(-> & <- & _) | (s2' & _ & Hs)].
  - exfalso. pose proof (Hw k eq_refl HmT). lia.
  - exact (Hpo s1 s2' k Hs HmT Hle j Hj).
Qed.

(* THE PROMPT BYTE: every waited stage has fixed its source and written it *)
Lemma prompt_okN_prompt md sel k :
  prompt_okN md sel ->
  (forall j, j < k -> exists s, md (WLeft j) = Some s /\ cntN sel (WLeft j) = length s) ->
  prompt_okN md (sel ++ [WSh k]).
Proof using.
  intros Hpo Hall s1 s2 k' Hsel HmT Hle j Hj.
  destruct (app_cons_eq_snoc s1 s2 sel (WSh k') (WSh k) (eq_sym Hsel))
    as [(-> & Hq & _) | (s2' & _ & Hs)].
  - injection Hq as ->. exact (Hall j Hj).
  - exact (Hpo s1 s2' k' Hs HmT Hle j Hj).
Qed.

(* a fire or a silence fixes an unfired source: nothing written moves *)
Lemma prompt_okN_mdupd md sel w s :
  md w = None -> w ∉ sel -> prompt_okN md sel -> prompt_okN (mdupd md w s) sel.
Proof using.
  intros Hw Hws Hpo s1 s2 k Hsel HmT Hle j Hj.
  (* the terminal writer at a split has written: it is not the one firing *)
  assert (HkW : WSh k <> w).
  { intros <-. apply Hws. rewrite Hsel. apply elem_of_app. right. apply elem_of_list_here. }
  assert (HmT' : md (WSh k) = Some alt_forkc).
  { unfold mdupd in HmT. rewrite decide_False in HmT; [exact HmT | exact HkW]. }
  destruct (Hpo s1 s2 k Hsel HmT' Hle j Hj) as (s' & Hs' & Hc).
  exists s'. split; [| exact Hc]. unfold mdupd. rewrite decide_False; [exact Hs' |].
  intros <-. rewrite Hw in Hs'. discriminate Hs'.
Qed.

(* THE TERMINAL SOURCE: sh node k's fork line and the prompt after it *)
Definition termw (w : wid) (s : bytes) : bool :=
  match w with WSh _ => bool_decide (s = alt_forkc) | _ => false end.

Lemma termw_true w s : termw w s = true -> exists k, w = WSh k /\ s = alt_forkc.
Proof using.
  destruct w as [k | k |]; cbn [termw]; [| discriminate | discriminate].
  intros H. apply bool_decide_eq_true in H. exists k. done.
Qed.
