(* ===================================================================== *)
(*  PipesDecE.v -- THE PIPELINE DISCIPLINE AT [pipes_lmE] IS DECIDABLE    *)
(*  (cut C8), so the ledger [PipesOut.pipesE_led] can case on it.         *)
(*                                                                       *)
(*  Two finite searches, neither ever run:                               *)
(*   - D4's mergeable outputs ([PipesDisc.pl_merge]) quantify over EVERY  *)
(*     admitted line.  At [adm_echo] the console parts of a terminal run  *)
(*     are diagnostics only (the producer: [dg_execL] or nothing; a       *)
(*     middle cat: [dg_execR], nothing or [cat_dg_write]; the failing     *)
(*     node: [dg_fork_b]; the stray: one of the same), and every sequence *)
(*     of middle outcomes is realisable, so a mergeable output is a       *)
(*     prefix of an interleaving of such streams, the prompt after all    *)
(*     of them.  [pde_chk] tests that, starting a middle stream only when *)
(*     a byte needs it ([pl_merge_spec]).                                 *)
(*   - the resolutions: [EchoDisc.disc_seg'_dec] at the model -- the      *)
(*     choice list canonicalised through [plalt_of] onto a finite per-    *)
(*     line candidate list, the prologue onto [EchoDisc.pro_cands].       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list list_numbers bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel PipeDisc.
Require Import ProgTree PipesPair PipesDisc PipesDiscDec LineModelLinks.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Local Notation fcE := (fun _ : bytes => @None bytes).

(* ===================================================================== *)
(*  1.  MERGES, ENUMERATED                                                *)
(* ===================================================================== *)

Definition pde_total (ss : list bytes) : nat := length (concat ss).

Lemma pde_total_insert (ss : list bytes) (i : nat) (y z : bytes) :
  ss !! i = Some y -> pde_total (<[i:=z]> ss) + length y = pde_total ss + length z.
Proof using.
  unfold pde_total. revert i. induction ss as [| a ss IH]; intros [| i] H;
    simpl in H; try discriminate.
  - injection H as ->. simpl. rewrite !length_app. lia.
  - simpl. rewrite !length_app. specialize (IH i H). lia.
Qed.

Lemma pde_concat_nils (ss : list bytes) : Forall (fun s => s = []) ss -> concat ss = [].
Proof using. induction 1 as [| s ss Hs _ IH]; [done |]. by rewrite /= Hs IH. Qed.

Lemma pde_merge_len (ss : list bytes) (b : bytes) : merge_all ss b -> length b = pde_total ss.
Proof using.
  induction 1 as [ss HF | ss i x s b Hi Hm IH].
  - by rewrite /pde_total pde_concat_nils.
  - pose proof (pde_total_insert ss i (x :: s) s Hi) as Ht. cbn [length] in *. rewrite -IH in Ht. lia.
Qed.

Fixpoint pde_merges_n (n : nat) (ss : list bytes) : list bytes :=
  (if decide (Forall (fun s => s = []) ss) then [[]] else []) ++
  match n with
  | 0 => []
  | S n' =>
      mjoin ((fun i => match ss !! i with
                       | Some (x :: s) => cons x <$> pde_merges_n n' (<[i:=s]> ss)
                       | _ => []
                       end) <$> seq 0 (length ss))
  end.

Lemma pde_merges_n_sound (n : nat) (ss : list bytes) (b : bytes) :
  b ∈ pde_merges_n n ss -> merge_all ss b.
Proof using.
  revert ss b. induction n as [| n IH]; intros ss b Hb; cbn [pde_merges_n] in Hb;
    apply elem_of_app in Hb as [Hb | Hb].
  - case_decide; [| by apply elem_of_nil in Hb].
    apply elem_of_list_singleton in Hb as ->. by apply ma_done.
  - by apply elem_of_nil in Hb.
  - case_decide; [| by apply elem_of_nil in Hb].
    apply elem_of_list_singleton in Hb as ->. by apply ma_done.
  - apply elem_of_list_join in Hb as (L & Hb & HL).
    apply elem_of_list_fmap in HL as (i & -> & _). cbv beta in Hb.
    destruct (ss !! i) as [[| x s] |] eqn:Hi; try by apply elem_of_nil in Hb.
    apply elem_of_list_fmap in Hb as (b' & -> & Hb').
    exact (ma_take ss i x s b' Hi (IH _ _ Hb')).
Qed.

Lemma pde_merges_n_complete (ss : list bytes) (b : bytes) :
  merge_all ss b -> forall n, length b <= n -> b ∈ pde_merges_n n ss.
Proof using.
  induction 1 as [ss HF | ss i x s b Hi Hm IH]; intros n Hn.
  - destruct n; cbn [pde_merges_n]; apply elem_of_app; left;
      (rewrite decide_True; [apply elem_of_list_here | exact HF]).
  - destruct n as [| n]; [simpl in Hn; lia |]. cbn [pde_merges_n]. apply elem_of_app. right.
    apply elem_of_list_join. exists (cons x <$> pde_merges_n n (<[i:=s]> ss)). split.
    + apply elem_of_list_fmap. exists b. split; [reflexivity | apply IH; simpl in Hn; lia].
    + apply elem_of_list_fmap. exists i. split; [cbv beta; by rewrite Hi |].
      apply elem_of_seq. split; [lia | exact (lookup_lt_Some _ _ _ Hi)].
Qed.

Definition pde_merges (ss : list bytes) : list bytes := pde_merges_n (pde_total ss) ss.

Lemma elem_of_pde_merges (ss : list bytes) (b : bytes) : b ∈ pde_merges ss <-> merge_all ss b.
Proof using.
  split; [apply pde_merges_n_sound |].
  intros H. apply (pde_merges_n_complete ss b H). by rewrite (pde_merge_len ss b H).
Qed.

Lemma pde_merge_cons_inv (ss : list bytes) (x : bv 8) (b : bytes) :
  merge_all ss (x :: b) -> exists i s, ss !! i = Some (x :: s) /\ merge_all (<[i:=s]> ss) b.
Proof using. intros H. inversion H; subst; eauto. Qed.

(* ===================================================================== *)
(*  2.  A PREFIX OF A TERMINAL BLOCK, AS ONE RELATION                     *)
(*                                                                       *)
(*  [pde_pmt W pr s u]: [u] is a prefix of an interleaving of the merge  *)
(*  of [W] followed by [pr], with [s].                                   *)
(* ===================================================================== *)
Inductive pde_pmt : list bytes -> bytes -> bytes -> bytes -> Prop :=
  | pmt_nil W pr s : pde_pmt W pr s []
  | pmt_w W pr s i x t u :
      W !! i = Some (x :: t) -> pde_pmt (<[i:=t]> W) pr s u -> pde_pmt W pr s (x :: u)
  | pmt_p W pr s x u :
      Forall (fun y => y = []) W -> pde_pmt W pr s u -> pde_pmt W (x :: pr) s (x :: u)
  | pmt_s W pr s x u : pde_pmt W pr s u -> pde_pmt W pr (x :: s) (x :: u).

Lemma pde_blk_pmt (W : list bytes) (Wm pr s b u : bytes) :
  merge_all W Wm -> merge_all [Wm ++ pr; s] b -> u `prefix_of` b -> pde_pmt W pr s u.
Proof using.
  revert W Wm pr s b. induction u as [| x u IH]; intros W Wm pr s b HW Hb Hu;
    [constructor |].
  destruct Hu as [k ->]. simpl in Hb.
  apply pde_merge_cons_inv in Hb as (i & r & Hi & Hm).
  destruct i as [| [| i]]; simpl in Hi; try discriminate.
  - injection Hi as Hi. destruct Wm as [| y Wm'].
    + simpl in Hi. subst pr. apply pmt_p; [exact (merge_all_nil_inv _ HW) |].
      apply (IH W [] r s (u ++ k)); [exact HW | exact Hm | by exists k].
    + simpl in Hi. injection Hi as -> Hr. subst r.
      apply pde_merge_cons_inv in HW as (j & t & Hj & HW').
      apply (pmt_w W pr s j x t); [exact Hj |].
      apply (IH (<[j:=t]> W) Wm' pr s (u ++ k)); [exact HW' | exact Hm | by exists k].
  - injection Hi as ->. apply pmt_s.
    apply (IH W Wm pr r (u ++ k)); [exact HW | exact Hm | by exists k].
Qed.

Lemma pde_pmt_blk (W : list bytes) (pr s u : bytes) :
  pde_pmt W pr s u ->
  exists Wm b, merge_all W Wm /\ merge_all [Wm ++ pr; s] b /\ u `prefix_of` b.
Proof using.
  induction 1 as [W pr s | W pr s i x t u Hi H (Wm & b & HW & Hb & Hu)
                 | W pr s x u HF H (Wm & b & HW & Hb & Hu) | W pr s x u H (Wm & b & HW & Hb & Hu)].
  - exists (concat W), (concat [concat W ++ pr; s]).
    split; [apply merge_all_concat |]. split; [apply merge_all_concat | apply prefix_nil].
  - exists (x :: Wm), (x :: b). split; [exact (ma_take W i x t Wm Hi HW) |].
    split; [apply (ma_take _ 0 x (Wm ++ pr)); [reflexivity | exact Hb] | by apply prefix_cons].
  - pose proof (merge_all_of_nils _ _ HF HW) as ->.
    exists [], (x :: b). split; [exact HW |].
    split; [apply (ma_take _ 0 x pr); [reflexivity | exact Hb] | by apply prefix_cons].
  - exists Wm, (x :: b). split; [exact HW |].
    split; [apply (ma_take _ 1 x s); [reflexivity | exact Hb] | by apply prefix_cons].
Qed.

Lemma pde_pmt_stray (W : list bytes) (pr sp s u : bytes) :
  pde_pmt W pr sp u -> sp `prefix_of` s -> pde_pmt W pr s u.
Proof using.
  intros H. revert s. induction H as [W pr sp | W pr sp i x t u Hi H IH
                                     | W pr sp x u HF H IH | W pr sp x u H IH]; intros s' Hs.
  - constructor.
  - exact (pmt_w W pr s' i x t u Hi (IH s' Hs)).
  - exact (pmt_p W pr s' x u HF (IH s' Hs)).
  - destruct Hs as [k ->]. apply pmt_s. apply IH. by exists k.
Qed.

Lemma pde_pmt_drop (W E : list bytes) (pr s u : bytes) :
  pde_pmt (W ++ E) pr s u -> Forall (fun y => y = []) E -> pde_pmt W pr s u.
Proof using.
  intros H HE. remember (W ++ E) as Z eqn:HZ. revert W HZ.
  induction H as [Z pr s | Z pr s i x t u Hi H IH | Z pr s x u HF H IH | Z pr s x u H IH];
    intros W' HZ; subst Z; unfold bytes in *.
  - constructor.
  - destruct (decide (i < length W')) as [Hl | Hl].
    + rewrite lookup_app_l in Hi; [| lia].
      apply (pmt_w W' pr s i x t u Hi). apply IH.
      rewrite insert_app_l; [reflexivity | lia].
    + rewrite lookup_app_r in Hi; [| lia].
      pose proof (Forall_lookup_1 _ _ _ _ HE Hi) as Hq. discriminate Hq.
  - apply Forall_app in HF as [HF _]. exact (pmt_p W' pr s x u HF (IH W' eq_refl)).
  - exact (pmt_s W' pr s x u (IH W' eq_refl)).
Qed.

(* ---- permutations ---- *)
Lemma pde_insert_perm {A} (l : list A) (i : nat) (y t : A) :
  l !! i = Some y -> <[i:=t]> l ≡ₚ t :: delete i l.
Proof using.
  revert i. induction l as [| a l IH]; intros [| i] H; simpl in H; try discriminate; simpl.
  - reflexivity.
  - rewrite (IH i H). apply perm_swap.
Qed.

Lemma pde_perm_insert {A} (W Z : list A) (i j : nat) (y t : A) :
  W ≡ₚ Z -> W !! i = Some y -> Z !! j = Some y -> <[i:=t]> W ≡ₚ <[j:=t]> Z.
Proof using.
  intros HP Hi Hj.
  rewrite (pde_insert_perm W i y t Hi) (pde_insert_perm Z j y t Hj).
  apply perm_skip. apply (Permutation_cons_inv (a := y)).
  rewrite -(delete_Permutation W i y Hi) -(delete_Permutation Z j y Hj). exact HP.
Qed.

Lemma pde_pmt_perm (W W' : list bytes) (pr s u : bytes) :
  pde_pmt W pr s u -> W ≡ₚ W' -> pde_pmt W' pr s u.
Proof using.
  intros H. revert W'.
  induction H as [W pr s | W pr s i x t u Hi H IH | W pr s x u HF H IH | W pr s x u H IH];
    intros W' HP.
  - constructor.
  - assert (Hin : (x :: t) ∈ W') by (rewrite -HP; exact (elem_of_list_lookup_2 _ _ _ Hi)).
    apply elem_of_list_lookup_1 in Hin as [j Hj].
    apply (pmt_w W' pr s j x t u Hj). apply IH.
    exact (pde_perm_insert W W' i j (x :: t) t HP Hi Hj).
  - apply pmt_p; [| exact (IH W' HP)].
    apply Forall_forall. intros y Hy. rewrite -HP in Hy.
    exact (proj1 (Forall_forall _ _) HF y Hy).
  - exact (pmt_s W' pr s x u (IH W' HP)).
Qed.

(* ===================================================================== *)
(*  3.  THE CHECKER                                                       *)
(* ===================================================================== *)
Definition pde_midok (m : bytes) : Prop := m = dg_execR \/ m = [] \/ m = cat_dg_write.

Fixpoint pde_chk (op : list bytes) (cm : bool) (sr pr u : bytes) {struct u} : bool :=
  match u with
  | [] => true
  | x :: u' =>
      existsb (fun j => match op !! j with
                        | Some (y :: t) => bool_decide (y = x) && pde_chk (<[j:=t]> op) cm sr pr u'
                        | _ => false
                        end) (seq 0 (length op))
      || (cm && existsb (fun m => match m with
                                  | y :: t => bool_decide (y = x) && pde_chk (op ++ [t]) cm sr pr u'
                                  | [] => false
                                  end) [dg_execR; cat_dg_write])
      || match sr with
         | y :: sr' => bool_decide (y = x) && pde_chk op cm sr' pr u'
         | [] => false
         end
      || (bool_decide (Forall (fun y => y = []) op)
          && match pr with
             | y :: pr' => bool_decide (y = x) && pde_chk op false sr pr' u'
             | [] => false
             end)
  end.

Lemma pde_insert_snoc (l : list bytes) (m t : bytes) : <[length l:=t]> (l ++ [m]) = l ++ [t].
Proof using. induction l as [| a l IH]; [done |]. simpl. by rewrite IH. Qed.

Lemma pde_chk_sound (u : bytes) : forall (op : list bytes) (cm : bool) (sr pr : bytes),
  pde_chk op cm sr pr u = true ->
  exists Mu, Forall (fun m => cm = true /\ (m = dg_execR \/ m = cat_dg_write)) Mu
             /\ pde_pmt (op ++ Mu) pr sr u.
Proof using.
  induction u as [| x u IH]; intros op cm sr pr Hc.
  { exists []. split; constructor. }
  cbn [pde_chk] in Hc. rewrite !orb_true_iff in Hc.
  destruct Hc as [[[HA | HB] | HC] | HD].
  - apply existsb_exists in HA as (j & _ & Hj). cbv beta in Hj.
    destruct (op !! j) as [[| y t] |] eqn:Hoj; try discriminate.
    apply andb_true_iff in Hj as [Hy Hr]. apply bool_decide_eq_true in Hy. subst y.
    destruct (IH _ _ _ _ Hr) as (Mu & HF & Hp). exists Mu. split; [exact HF |].
    pose proof (lookup_lt_Some _ _ _ Hoj) as Hlt.
    apply (pmt_w (op ++ Mu) pr sr j x t u); [by rewrite lookup_app_l |].
    by rewrite insert_app_l.
  - apply andb_true_iff in HB as [Hcm HB]. apply existsb_exists in HB as (m & Hm & Hr).
    destruct m as [| y t]; cbv beta iota in Hr; [discriminate |].
    apply andb_true_iff in Hr as [Hy Hr]. apply bool_decide_eq_true in Hy. subst y.
    destruct (IH _ _ _ _ Hr) as (Mu & HF & Hp).
    exists (Mu ++ [x :: t]). split.
    + apply Forall_app. split; [exact HF |]. apply Forall_singleton. split; [exact Hcm |].
      destruct Hm as [<- | [<- | []]]; [by left | by right].
    + rewrite app_assoc.
      apply (pmt_w ((op ++ Mu) ++ [x :: t]) pr sr (length (op ++ Mu)) x t u).
      * by apply list_lookup_middle.
      * rewrite pde_insert_snoc. apply (pde_pmt_perm _ _ _ _ _ Hp).
        rewrite -!app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
  - destruct sr as [| y sr']; [discriminate |].
    apply andb_true_iff in HC as [Hy Hr]. apply bool_decide_eq_true in Hy. subst y.
    destruct (IH _ _ _ _ Hr) as (Mu & HF & Hp). exists Mu. split; [exact HF |].
    by apply pmt_s.
  - apply andb_true_iff in HD as [He HD]. apply bool_decide_eq_true in He.
    destruct pr as [| y pr']; [discriminate |].
    apply andb_true_iff in HD as [Hy Hr]. apply bool_decide_eq_true in Hy. subst y.
    destruct (IH _ _ _ _ Hr) as (Mu & HF & Hp).
    destruct Mu as [| m Mu]; [| apply Forall_cons in HF as [[Hf _] _]; discriminate Hf].
    exists []. split; [constructor |]. apply pmt_p; [by rewrite app_nil_r | exact Hp].
Qed.

Lemma pde_chk_complete (W : list bytes) (pr sr u : bytes) :
  pde_pmt W pr sr u ->
  forall (op Mu : list bytes) (cm : bool),
    W ≡ₚ op ++ Mu ->
    Forall (fun m => if cm then pde_midok m else m = []) Mu ->
    pde_chk op cm sr pr u = true.
Proof using.
  induction 1 as [W pr sr | W pr sr i x t u Hi H IH | W pr sr x u HF H IH | W pr sr x u H IH];
    intros op Mu cm HP HMu; [reflexivity | | |]; unfold bytes in *.
  - assert (Hin : (x :: t) ∈ op ++ Mu)
      by (rewrite -HP; exact (elem_of_list_lookup_2 _ _ _ Hi)).
    cbn [pde_chk]. rewrite !orb_true_iff.
    apply elem_of_app in Hin as [Hin | Hin].
    + left. left. left. apply elem_of_list_lookup_1 in Hin as [j Hj].
      apply existsb_exists. exists j. split.
      { apply in_seq. split; [lia | exact (lookup_lt_Some _ _ _ Hj)]. }
      cbv beta. rewrite Hj. cbv beta iota. rewrite bool_decide_true; [| reflexivity]. cbn [andb].
      apply (IH (<[j:=t]> op) Mu cm); [| exact HMu].
      rewrite -insert_app_l; [| exact (lookup_lt_Some _ _ _ Hj)].
      apply (pde_perm_insert W (op ++ Mu) i j (x :: t) t HP Hi).
      rewrite lookup_app_l; [exact Hj | exact (lookup_lt_Some _ _ _ Hj)].
    + left. left. right. apply elem_of_list_lookup_1 in Hin as [k Hk].
      pose proof (Forall_lookup_1 _ _ _ _ HMu Hk) as Hmk.
      destruct cm; cbv beta iota in Hmk; [| discriminate Hmk].
      apply andb_true_iff. split; [reflexivity |].
      apply existsb_exists. exists (x :: t). split.
      { destruct Hmk as [-> | [Hq | ->]]; [by left | discriminate Hq | by right; left]. }
      cbv beta iota. rewrite bool_decide_true; [| reflexivity]. cbn [andb].
      apply (IH (op ++ [t]) (delete k Mu) true); [| by apply Forall_delete].
      assert (Hl : (op ++ Mu) !! (length op + k) = Some (x :: t)).
      { rewrite lookup_app_r; [| lia].
        rewrite (_ : length op + k - length op = k); [exact Hk | lia]. }
      rewrite (pde_perm_insert W (op ++ Mu) i (length op + k) (x :: t) t HP Hi Hl).
      rewrite insert_app_r (pde_insert_perm Mu k (x :: t) t Hk) -app_assoc.
      apply Permutation_app_head. reflexivity.
  - cbn [pde_chk]. rewrite !orb_true_iff. right.
    assert (Hall : Forall (fun y => y = []) (op ++ Mu)).
    { apply Forall_forall. intros y Hy. rewrite -HP in Hy. exact (proj1 (Forall_forall _ _) HF y Hy). }
    apply Forall_app in Hall as [Hop HM].
    apply andb_true_iff. split; [by apply bool_decide_eq_true |].
    cbv beta iota. rewrite bool_decide_true; [| reflexivity]. cbn [andb].
    exact (IH op Mu false HP HM).
  - cbn [pde_chk]. rewrite !orb_true_iff. left. right.
    cbv beta iota. rewrite bool_decide_true; [| reflexivity]. cbn [andb]. exact (IH op Mu cm HP HMu).
Qed.

(* ===================================================================== *)
(*  4.  THE TERMINAL RUNS AT [adm_echo]: their shape and its realisation  *)
(* ===================================================================== *)
Lemma pde_prod_cons (L : bytes) (ws : list (list (bv 8))) (so : st_out) :
  stage_out fcE L (SProd (PrEcho ws)) so -> so_cons so = dg_execL \/ so_cons so = [].
Proof using. intros H. inversion H; subst; simpl; auto. Qed.

Lemma pde_mid_cons (L : bytes) (so : st_out) :
  stage_out fcE L SMid so -> pde_midok (so_cons so).
Proof using. intros H. unfold pde_midok. inversion H; subst; simpl; auto. Qed.

Lemma pde_sfx_shape (L : bytes) (m : nat) (win : wr_out) (wc : bool) (W : list bytes) (s : bytes) :
  sfx_term fcE L m win wc W s ->
  exists mids, W = mids ++ [dg_fork_b] /\ Forall pde_midok mids /\ pde_midok s.
Proof using.
  induction 1 as [m win wc so Hso | m win wc so W s Hso Hp Hsfx IH].
  - exists []. split; [reflexivity |]. split; [constructor | exact (pde_mid_cons _ _ Hso)].
  - destruct IH as (mids & -> & HF & Hs). exists (so_cons so :: mids).
    split; [reflexivity |]. split; [constructor; [exact (pde_mid_cons _ _ Hso) | exact HF] | exact Hs].
Qed.

Lemma pde_lterm_shape (l : pline') (W : list bytes) (s : bytes) :
  adm_echo l = true -> line_term fcE l W s ->
  (W = [dg_fork_b] /\ (s = dg_execL \/ s = []))
  \/ (exists p mids, W = p :: mids ++ [dg_fork_b] /\ (p = dg_execL \/ p = [])
                     /\ Forall pde_midok mids /\ pde_midok s).
Proof using.
  intros Ha H. revert Ha. destruct H as [p n so Hn Hso | p n so W0 s0 Hso Hsfx]; intros Ha.
  - left. split; [reflexivity |].
    destruct p as [ws | f]; [| discriminate Ha]. exact (pde_prod_cons _ _ _ Hso).
  - right. destruct p as [ws | f]; [| discriminate Ha].
    destruct (pde_sfx_shape _ _ _ _ _ _ Hsfx) as (mids & -> & HF & Hs).
    exists (so_cons so), mids. split; [reflexivity |].
    split; [exact (pde_prod_cons _ _ _ Hso) |]. split; [exact HF | exact Hs].
Qed.

Lemma pde_prod_so (p : bytes) :
  p = dg_execL \/ p = [] ->
  exists so, stage_out fcE (prod_content fcE (PrEcho [])) (SProd (PrEcho [])) so /\ so_cons so = p.
Proof using.
  intros [-> | ->]; eexists; split; [apply so_exec | reflexivity | apply so_silent | reflexivity].
Qed.

Lemma pde_mid_so (L : bytes) (m : bytes) :
  pde_midok m -> exists so, stage_out fcE L SMid so /\ so_cons so = m /\ rd_of so = RdGone.
Proof using.
  intros [-> | [-> | ->]]; eexists.
  - split; [apply so_exec | split; reflexivity].
  - split; [apply so_silent | split; reflexivity].
  - split; [eapply so_mid_halt, prefix_nil | split; reflexivity].
Qed.

Lemma pde_pairB_gone (L : bytes) (wc : bool) (w : wr_out) : pipe_pairB L wc w RdGone.
Proof using. destruct w; exact I. Qed.

Lemma pde_sfx_build (L : bytes) (mids : list bytes) (s : bytes) :
  Forall pde_midok mids -> pde_midok s ->
  forall win wc, sfx_term fcE L (S (S (length mids))) win wc (mids ++ [dg_fork_b]) s.
Proof using.
  intros HF Hs. induction HF as [| m mids Hm HF IH]; intros win wc.
  - destruct (pde_mid_so L s Hs) as (so & Hso & Hc & _). simpl. rewrite -Hc.
    apply stt_here. exact Hso.
  - destruct (pde_mid_so L m Hm) as (so & Hso & Hc & Hr). simpl. rewrite -Hc.
    eapply stt_next; [exact Hso | rewrite Hr; apply pde_pairB_gone | apply IH].
Qed.

Lemma pde_merge_of_lt (n : nat) (W : list bytes) (s u : bytes) :
  line_term fcE (LPipes (PrEcho []) n) W s -> pde_pmt W u_prompt s u ->
  pl_merge fcE adm_echo u.
Proof using.
  intros Hlt Hp. destruct (pde_pmt_blk _ _ _ _ Hp) as (Wm & b & HW & Hb & Hu).
  exists (LPipes (PrEcho []) n), b. split; [reflexivity |]. split; [| exact Hu].
  split.
  - intros ->. pose proof (pde_merge_len _ _ Hb) as Hl. unfold pde_total in Hl.
    simpl in Hl. rewrite !length_app ll_prompt_len in Hl. simpl in Hl. lia.
  - exists b. split; [| reflexivity]. exists W, s, Wm, s.
    split; [exact Hlt |]. split; [exact HW |]. split; [reflexivity | exact Hb].
Qed.

(* ===================================================================== *)
(*  5.  [pl_merge] AT [adm_echo], DECIDED                                 *)
(* ===================================================================== *)
Definition pde_mergeb (u : bytes) : bool :=
  existsb (fun p => existsb (fun s => pde_chk [p; dg_fork_b] true s u_prompt u)
                      [dg_execR; []; cat_dg_write]) [[]; dg_execL]
  || existsb (fun s => pde_chk [dg_fork_b] false s u_prompt u) [dg_execL; []].

Lemma pl_merge_spec (u : bytes) : pl_merge fcE adm_echo u <-> pde_mergeb u = true.
Proof using.
  split.
  - intros (l & b & Ha & [_ (b' & (W & s & Wm & sp & Hlt & HW & Hsp & Hb) & Hbb)] & Hu).
    pose proof (pde_pmt_stray _ _ _ _ _
                  (pde_blk_pmt W Wm u_prompt sp b' u HW Hb
                     ltac:(etrans; [exact Hu | exact Hbb])) Hsp) as Hp.
    unfold pde_mergeb. apply orb_true_iff.
    destruct (pde_lterm_shape l W s Ha Hlt) as [[-> Hs] | (p & mids & -> & Hpp & HF & Hs)].
    + right. apply existsb_exists. exists s. split.
      { destruct Hs as [-> | ->]; [left | right; left]; reflexivity. }
      apply (pde_chk_complete _ _ _ _ Hp [dg_fork_b] [] false); [by rewrite app_nil_r | constructor].
    + left. apply existsb_exists. exists p. split.
      { destruct Hpp as [-> | ->]; [right; left | left]; reflexivity. }
      apply existsb_exists. exists s. split.
      { destruct Hs as [-> | [-> | ->]]; [left | right; left | right; right; left]; reflexivity. }
      apply (pde_chk_complete _ _ _ _ Hp [p; dg_fork_b] mids true); [| exact HF].
      simpl. apply perm_skip. rewrite Permutation_app_comm. reflexivity.
  - intros Hc. unfold pde_mergeb in Hc. apply orb_true_iff in Hc as [Hc | Hc].
    + apply existsb_exists in Hc as (p & Hpin & Hc).
      apply existsb_exists in Hc as (s & Hsin & Hc).
      assert (Hpp : p = dg_execL \/ p = []).
      { destruct Hpin as [<- | [<- | []]]; [right | left]; reflexivity. }
      assert (Hs : pde_midok s).
      { unfold pde_midok. destruct Hsin as [<- | [<- | [<- | []]]]; auto. }
      destruct (pde_chk_sound u [p; dg_fork_b] true s u_prompt Hc) as (Mu & HF & Hp).
      apply (pde_merge_of_lt (S (S (length Mu))) (p :: Mu ++ [dg_fork_b]) s u).
      * destruct (pde_prod_so p Hpp) as (so & Hso & Hc'). rewrite -Hc'.
        eapply lt_next; [exact Hso |].
        apply pde_sfx_build; [| exact Hs].
        eapply Forall_impl; [exact HF |]. intros m [_ [-> | ->]]; unfold pde_midok; auto.
      * apply (pde_pmt_perm _ _ _ _ _ Hp). simpl. apply perm_skip.
        rewrite Permutation_app_comm. reflexivity.
    + apply existsb_exists in Hc as (s & Hsin & Hc).
      assert (Hs : s = dg_execL \/ s = []).
      { destruct Hsin as [<- | [<- | []]]; [left | right]; reflexivity. }
      destruct (pde_chk_sound u [dg_fork_b] false s u_prompt Hc) as (Mu & HF & Hp).
      destruct Mu as [| m Mu]; [| apply Forall_cons in HF as [[Hf _] _]; discriminate Hf].
      apply (pde_merge_of_lt 1 [dg_fork_b] s u); [| by rewrite app_nil_r in Hp].
      destruct (pde_prod_so s Hs) as (so & Hso & Hc'). rewrite -Hc'.
      apply lt_here; [lia | exact Hso].
Qed.

Global Instance pl_mergeE_dec (u : bytes) : Decision (pl_merge fcE adm_echo u).
Proof using.
  destruct (pde_mergeb u) eqn:H; [left; by apply pl_merge_spec |].
  right. intros Hm. apply pl_merge_spec in Hm. congruence.
Qed.


(* ===================================================================== *)
(*  6.  THE CHOICE LIST IS READ ONLY THROUGH ITS DECODING                 *)
(* ===================================================================== *)
Section dec_ext.
  Context (M : lmodel).

  Lemma pde_pro_idx_ext (cs1 cs2 : list nat) :
    (forall j, lm_at M cs1 j = lm_at M cs2 j) ->
    forall q, lm_pro_idx M cs1 q = lm_pro_idx M cs2 q.
  Proof using.
    intros H q. induction q as [| q IH]; [reflexivity |].
    rewrite !lm_pro_idx_S IH H. reflexivity.
  Qed.

  Lemma pde_upto_ext (cs1 cs2 : list nat) (s : lm_st M) (bs : list (list (bv 8))) :
    (forall j, lm_at M cs1 j = lm_at M cs2 j) ->
    forall q, lm_upto M cs1 s bs q = lm_upto M cs2 s bs q.
  Proof using.
    intros H q. induction q as [| q IH]; [reflexivity |].
    cbn [lm_upto]. rewrite IH H. reflexivity.
  Qed.

  Lemma pde_cont_at_ext (ps cs1 cs2 : list nat) (s : lm_st M) (bs : list (list (bv 8))) (i : nat) :
    (forall j, lm_at M cs1 j = lm_at M cs2 j) ->
    lm_cont_at M ps cs1 s bs i = lm_cont_at M ps cs2 s bs i.
  Proof using.
    intros H. rewrite /lm_cont_at (pde_upto_ext cs1 cs2 s bs H i) (H i)
      (pde_pro_idx_ext cs1 cs2 H i). reflexivity.
  Qed.

  Lemma pde_seq_ext (ps cs1 cs2 : list nat) (s : lm_st M) (bs : list (list (bv 8))) (q : nat) :
    (forall j, lm_at M cs1 j = lm_at M cs2 j) ->
    lm_seq M ps cs1 s bs q = lm_seq M ps cs2 s bs q.
  Proof using.
    intros H. induction q as [| q IH]; [reflexivity |].
    rewrite !lm_seq_S IH /lm_blk (pde_cont_at_ext ps cs1 cs2 s bs q H). reflexivity.
  Qed.

  Lemma pde_sess_ext (ps cs1 cs2 : list nat) (s : lm_st M) (I : list (bv 8)) :
    (forall j, lm_at M cs1 j = lm_at M cs2 j) ->
    lm_sess M ps cs1 s I = lm_sess M ps cs2 s I.
  Proof using. intros H. by rewrite /lm_sess (pde_seq_ext ps cs1 cs2 s _ _ H). Qed.

  Lemma pde_d4_ext (cs1 cs2 : list nat) (s : lm_st M) (I : list (bv 8)) :
    (forall j, lm_at M cs1 j = lm_at M cs2 j) ->
    lm_d4 M cs2 s I -> lm_d4 M cs1 s I.
  Proof using.
    intros H Hd i Hi Hex Hm. rewrite (pde_upto_ext cs1 cs2 s _ H i) in Hex.
    apply (Hd i Hi Hex).
    by rewrite -(pde_upto_ext cs1 cs2 s _ H i) -(H i).
  Qed.

  (* ---- the prologue is read only at the rounds the transcript enters ---- *)
  Lemma pde_seq_ps_ext (ps1 ps2 cs : list nat) (s : lm_st M) (bs : list (list (bv 8))) (q : nat) :
    (forall r, r <= lm_pro_idx M cs q -> pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
    lm_seq M ps1 cs s bs q = lm_seq M ps2 cs s bs q.
  Proof using.
    induction q as [| q IH]; intros H; [reflexivity |].
    rewrite !lm_seq_S IH;
      [| intros r Hr; apply H; pose proof (lm_pro_idx_mono M cs q (S q) ltac:(lia)); lia].
    f_equal. rewrite /lm_blk /lm_cont_at.
    destruct (lm_panic M (lm_at M cs q)) eqn:Hp; [| reflexivity].
    rewrite (H (S (lm_pro_idx M cs q))); [reflexivity |].
    rewrite (lm_pro_idx_Sp M cs q Hp). lia.
  Qed.

  Lemma pde_sess_ps_ext (ps1 ps2 cs : list nat) (s : lm_st M) (I : list (bv 8)) :
    (forall r, r <= lm_pro_idx M cs (nlines I) -> pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
    lm_sess M ps1 cs s I = lm_sess M ps2 cs s I.
  Proof using.
    intros H. assert (E : pro_of ps1 = pro_of ps2) by exact (H 0 ltac:(lia)).
    rewrite /lm_sess E (pde_seq_ps_ext ps1 ps2 cs s _ _ H). reflexivity.
  Qed.

  Lemma pde_seq_pro_len (ps cs : list nat) (s : lm_st M) (bs : list (list (bv 8))) (q : nat) :
    forall r, r <= lm_pro_idx M cs q ->
    length (pro_of (pro_from r ps)) <= length (pro_of ps) + length (lm_seq M ps cs s bs q).
  Proof using.
    induction q as [| q IH]; intros r Hr.
    - assert (r = 0) by (cbn in Hr; lia). subst r. cbn [pro_from]. lia.
    - rewrite lm_seq_S length_app.
      destruct (decide (r <= lm_pro_idx M cs q)) as [Hle | Hgt];
        [pose proof (IH r Hle); lia |].
      destruct (lm_panic M (lm_at M cs q)) eqn:Hp.
      + rewrite (lm_pro_idx_Sp M cs q Hp) in Hr.
        assert (r = S (lm_pro_idx M cs q)) as -> by lia.
        rewrite /lm_blk /lm_cont_at Hp !length_app. cbn [length]. rewrite !length_app. lia.
      + rewrite (lm_pro_idx_Sn M cs q Hp) in Hr. lia.
  Qed.

  Lemma pde_sess_pro_len (ps cs : list nat) (s : lm_st M) (I : list (bv 8)) (r : nat) :
    r <= lm_pro_idx M cs (nlines I) ->
    length (pro_of (pro_from r ps)) <= length (lm_sess M ps cs s I).
  Proof using.
    intros Hr. rewrite /lm_sess !length_app.
    pose proof (pde_seq_pro_len ps cs s (bodies_of I) (nlines I) r Hr). lia.
  Qed.
End dec_ext.

(* ===================================================================== *)
(*  7.  THE CANDIDATE CODES OF A LINE                                     *)
(* ===================================================================== *)
Local Notation PME := pipes_lmE.

Definition pde_cands (l : pline') : list nat :=
  [plalt_code PLPanic; plalt_code (PLRun []); plalt_code (PLRun (pl_exfb l))]
  ++ ((fun b => plalt_code (PLRun b)) <$> (line_runs fcE l ≫= pde_merges))
  ++ ((fun b => plalt_code (PLTerm b)) <$>
        (line_terms fcE l ≫= fun ws =>
           pde_merges ws.1 ≫= fun Wm =>
           prefixes ws.2 ≫= fun sp =>
           pde_merges [Wm ++ u_prompt; sp] ≫= prefixes)).

Lemma pde_cands_complete (l : pline') (a : plalt) :
  lm_ok PME tt l a -> plalt_code a ∈ pde_cands l.
Proof using.
  intros H. cbn [lm_ok pipes_lmE pipes_lm] in H. rewrite /pde_cands.
  destruct H as [[-> | [-> | ->]] | [_ Hok]].
  - apply elem_of_app. left. apply elem_of_list_here.
  - apply elem_of_app. left. apply elem_of_list_further, elem_of_list_here.
  - apply elem_of_app. left. apply elem_of_list_further, elem_of_list_further, elem_of_list_here.
  - destruct a as [| b | b].
    + apply elem_of_app. left. apply elem_of_list_here.
    + destruct Hok as (ss & Hr & Hm).
      apply elem_of_app. right. apply elem_of_app. left.
      apply elem_of_list_fmap. exists b. split; [reflexivity |].
      apply elem_of_list_bind. exists ss.
      split; [by apply elem_of_pde_merges | by apply line_runs_spec].
    + destruct Hok as [_ (b' & (W & s & Wm & sp & Hlt & HW & Hsp & Hb) & Hbb)].
      apply elem_of_app. right. apply elem_of_app. right.
      apply elem_of_list_fmap. exists b. split; [reflexivity |].
      apply elem_of_list_bind. exists (W, s). split; [| by apply line_terms_spec].
      apply elem_of_list_bind. exists Wm. split; [| by apply elem_of_pde_merges].
      apply elem_of_list_bind. exists sp. split; [| by apply prefixes_spec].
      apply elem_of_list_bind. exists b'. split; [by apply prefixes_spec | by apply elem_of_pde_merges].
Qed.

Fixpoint pde_prod (Ls : list (list nat)) : list (list nat) :=
  match Ls with
  | [] => [[]]
  | L :: Ls' => L ≫= fun c => cons c <$> pde_prod Ls'
  end.

Lemma pde_prod_intro (cs : list nat) (Ls : list (list nat)) :
  Forall2 (fun c L => c ∈ L) cs Ls -> cs ∈ pde_prod Ls.
Proof using.
  induction 1 as [| c L cs Ls Hc _ IH]; [by apply elem_of_list_singleton |].
  cbn [pde_prod]. apply elem_of_list_bind. exists c. split; [| exact Hc].
  apply elem_of_list_fmap. exists cs. split; [reflexivity | exact IH].
Qed.

(* ===================================================================== *)
(*  8.  THE PIECES, DECIDED                                               *)
(* ===================================================================== *)
Local Instance pde_merge_dec (u : list (bv 8)) : Decision (lm_merge PME u) := pl_mergeE_dec u.

Local Instance pde_input_dec (I : list (bv 8)) : Decision (lm_disc_input PME I).
Proof using. rewrite /lm_disc_input. cbn [lm_body_ok lm_body_byte pipes_lmE pipes_lm]. apply _. Qed.

Local Instance pde_ok_dec (l : pline') (a : plalt) : Decision (lm_ok PME tt l a) :=
  pipes_lm_ok_dec fcE adm_echo tt l a.

(* the model's range condition ignores the state: it is decided entry by
   entry ([LineModel.lm_alts_ok_nostate]) *)
Lemma pde_alts_iff (I : list (bv 8)) (cs : list nat) :
  lm_alts_ok PME tt I cs
  <-> Forall2 (fun l c => lm_ok PME tt l (lm_dec PME c)) (lm_of PME <$> bodies_of I) cs.
Proof using. exact (lm_alts_ok_nostate PME tt I cs (fun _ _ _ _ Hx => Hx)). Qed.

Local Instance pde_alts_dec (I : list (bv 8)) (cs : list nat) : Decision (lm_alts_ok PME tt I cs).
Proof using.
  destruct (decide (Forall2 (fun l c => lm_ok PME tt l (lm_dec PME c))
                      (lm_of PME <$> bodies_of I) cs)) as [H | H].
  - left. by apply pde_alts_iff.
  - right. intros H'. apply H. by apply pde_alts_iff.
Qed.

Definition pde_termex (l : pline') : Prop :=
  exists c, lm_ok PME tt l c /\ lm_term PME c = true.

Local Instance pde_termex_dec (l : pline') : Decision (pde_termex l).
Proof using.
  destruct (decide (Exists (fun c => lm_ok PME tt l (plalt_of c) /\ plterm (plalt_of c) = true)
                      (pde_cands l))) as [H | H].
  - left. apply Exists_exists in H as (c & _ & Hc). exists (plalt_of c). exact Hc.
  - right. intros (c & Hok & Ht). apply H. apply Exists_exists.
    exists (plalt_code c). split; [exact (pde_cands_complete l c Hok) |].
    rewrite plalt_of_code. split; [exact Hok | exact Ht].
Qed.

Lemma pde_d4_iff (cs : list nat) (I : list (bv 8)) :
  lm_d4 PME cs tt I <->
  Forall (fun i => pde_termex (lm_of PME (bodies_of I !!! i)) ->
                   lm_merge PME (lm_cont PME (lm_upto PME cs tt (bodies_of I) i)
                                   (lm_of PME (bodies_of I !!! i)) (lm_at PME cs i)) ->
                   nlines I = S i /\ rest_of I = []) (seq 0 (nlines I)).
Proof using.
  rewrite Forall_forall. split.
  - intros H i Hi (c & Hc) Hm. apply elem_of_seq in Hi.
    apply (H i ltac:(lia)); [exists c; exact Hc | exact Hm].
  - intros H i Hi (c & Hc) Hm.
    apply (H i); [apply elem_of_seq; lia | exists c; exact Hc | exact Hm].
Qed.

Local Instance pde_d4_dec (cs : list nat) (I : list (bv 8)) : Decision (lm_d4 PME cs tt I).
Proof using.
  destruct (decide (Forall (fun i => pde_termex (lm_of PME (bodies_of I !!! i)) ->
                   lm_merge PME (lm_cont PME (lm_upto PME cs tt (bodies_of I) i)
                                   (lm_of PME (bodies_of I !!! i)) (lm_at PME cs i)) ->
                   nlines I = S i /\ rest_of I = []) (seq 0 (nlines I)))) as [H | H].
  - left. by apply pde_d4_iff.
  - right. intros H'. apply H. by apply pde_d4_iff.
Qed.

Local Instance pde_pro_ok_dec (ps cs : list nat) (q : nat) : Decision (lm_pro_ok PME ps cs q).
Proof using. rewrite /lm_pro_ok. apply _. Qed.

Local Instance pde_pt_dec (ps cs : list nat) (p : list mobs) : Decision (lm_disc_pt PME ps cs tt p).
Proof using. rewrite /lm_disc_pt. apply _. Qed.

Definition pde_phi (seg : list mobs) (ps cs : list nat) : Prop :=
  lm_alts_ok PME tt (ins seg) cs /\ lm_d4 PME cs tt (ins seg)
  /\ Forall (fun p => lm_pro_ok PME ps cs (nlines (ins p)) /\ lm_disc_pt PME ps cs tt p)
       (in_pres seg).

Local Instance pde_phi_dec (seg : list mobs) (ps cs : list nat) : Decision (pde_phi seg ps cs).
Proof using. rewrite /pde_phi. apply _. Qed.

Definition pde_rhs (seg : list mobs) : Prop :=
  lm_disc_input PME (ins seg)
  /\ Exists (fun cs => Exists (fun ps => pde_phi seg ps cs)
                         (pro_cands (S (lm_pro_idx PME cs (nlines_max (in_pres seg)))) (length seg)))
       (pde_prod (pde_cands <$> (lm_of PME <$> bodies_of (ins seg)))).

Local Instance pde_rhs_dec (seg : list mobs) : Decision (pde_rhs seg).
Proof using. rewrite /pde_rhs. apply _. Qed.

(* ===================================================================== *)
(*  9.  THE SEARCH IS COMPLETE                                            *)
(* ===================================================================== *)
Lemma pde_seg_iff (seg : list mobs) : lm_disc_seg' PME tt seg <-> pde_rhs seg.
Proof using.
  split.
  - intros [Hin (ps & cs & Halts & Hd4 & Hall)]. split; [exact Hin |].
    pose (f := fun c => plalt_code (plalt_of c)).
    pose (cs0 := f <$> cs).
    assert (Hext : forall j, lm_at PME cs0 j = lm_at PME cs j).
    { intros j. rewrite /lm_at /cs0 !list_lookup_total_alt list_lookup_fmap.
      destruct (cs !! j) as [c |]; [exact (plalt_of_code (plalt_of c)) | reflexivity]. }
    pose proof (proj1 (pde_alts_iff _ _) Halts) as HaltsF.
    assert (Halts0 : lm_alts_ok PME tt (ins seg) cs0).
    { apply pde_alts_iff. rewrite /cs0. apply Forall2_fmap_r.
      eapply Forall2_impl; [exact HaltsF |]. intros l c Hok.
      change (lm_ok PME tt l (plalt_of (plalt_code (plalt_of c)))). rewrite plalt_of_code. exact Hok. }
    assert (Hprod : cs0 ∈ pde_prod (pde_cands <$> (lm_of PME <$> bodies_of (ins seg)))).
    { apply pde_prod_intro. rewrite /cs0. apply Forall2_fmap_l, Forall2_fmap_r, Forall2_flip.
      eapply Forall2_impl; [exact HaltsF |]. intros l c Hok.
      exact (pde_cands_complete l (plalt_of c) Hok). }
    assert (Hd40 : lm_d4 PME cs0 tt (ins seg)) by exact (pde_d4_ext PME cs0 cs tt _ Hext Hd4).
    assert (Hall0 : forall p, p ∈ in_pres seg ->
              lm_pro_ok PME ps cs0 (nlines (ins p)) /\ lm_disc_pt PME ps cs0 tt p).
    { intros p Hp. destruct (Hall p Hp) as [[HF Hlt] Hpt].
      rewrite /lm_pro_ok /lm_disc_pt (pde_pro_idx_ext PME cs0 cs Hext)
        (pde_sess_ext PME ps cs0 cs tt _ Hext).
      split; [split; [exact HF | exact Hlt] | exact Hpt]. }
    apply Exists_exists. exists cs0. split; [exact Hprod |]. apply Exists_exists.
    destruct (decide (in_pres seg = [])) as [Hz | Hz].
    { destruct (pro_cands_nonempty (S (lm_pro_idx PME cs0 (nlines_max (in_pres seg))))
                  (length seg)) as [g Hg].
      exists g. split; [exact Hg |]. split; [exact Halts0 |]. split; [exact Hd40 |].
      rewrite Hz. constructor. }
    destruct (nlines_max_mem (in_pres seg) Hz) as (pl & Hplin & Hpleq).
    destruct (Hall0 pl Hplin) as [[HFps Hltl] Hptl].
    assert (Hplp : pl `prefix_of` seg)
      by exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) pl Hplin).
    destruct (pro_canon (S (lm_pro_idx PME cs0 (nlines_max (in_pres seg))))
                (length seg) ps HFps) as (ps0 & Hin0 & Hrd0 & Hag0).
    { intros r Hr. rewrite -Hpleq in Hr. split; [lia |].
      etrans; [apply (pde_sess_pro_len PME ps cs0 tt (done_of (ins pl)) r);
               rewrite nlines_done; lia |].
      etrans; [apply prefix_length, Hptl |].
      etrans; [apply obs_wire_length |].
      exact (prefix_length _ _ Hplp). }
    exists ps0. split; [exact Hin0 |]. split; [exact Halts0 |]. split; [exact Hd40 |].
    apply Forall_forall. intros p Hp. destruct (Hall0 p Hp) as [[_ Hltp] Hptp].
    assert (Hidxle : lm_pro_idx PME cs0 (nlines (ins p))
                     <= lm_pro_idx PME cs0 (nlines_max (in_pres seg)))
      by (apply (lm_pro_idx_mono PME), nlines_max_ge, Hp).
    assert (Hsame : lm_sess PME ps0 cs0 tt (done_of (ins p))
                    = lm_sess PME ps cs0 tt (done_of (ins p))).
    { apply pde_sess_ps_ext. intros r Hr. rewrite nlines_done in Hr. apply Hag0. lia. }
    split.
    + split; [eapply pro_cands_Forall; exact Hin0 | lia].
    + rewrite /lm_disc_pt Hsame. exact Hptp.
  - intros [Hin HE]. apply Exists_exists in HE as (cs & _ & HE).
    apply Exists_exists in HE as (ps & _ & Halts & Hd4 & Hall).
    split; [exact Hin |]. exists ps, cs. split; [exact Halts |]. split; [exact Hd4 |].
    intros p Hp. exact (proj1 (Forall_forall _ _) Hall p Hp).
Qed.

Local Instance pde_seg_dec (seg : list mobs) :
  Decision (exists s : lm_st PME, lm_st_ok PME s /\ lm_disc_seg' PME s seg).
Proof using.
  destruct (decide (pde_rhs seg)) as [H | H].
  - left. exists tt. split; [exact I | by apply pde_seg_iff].
  - right. intros [[] [_ H']]. apply H. by apply pde_seg_iff.
Qed.

(* ===================================================================== *)
(*  THE INSTANCE                                                          *)
(* ===================================================================== *)
Global Instance lm_disc_pipesE_dec (h : list mobs) : Decision (lm_disc pipes_lmE h).
Proof using. rewrite /lm_disc. apply _. Qed.

