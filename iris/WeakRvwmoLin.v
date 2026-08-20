(** * WeakRvwmoLin.v — THE RULE-14 LINEARIZATION (T2-1c): graph → same-log cand

    Design: [claude-notes/design/weak-memory-tier2-s6.md]; the model is
    [WeakRvwmoGraph]'s RVWMO⁻ and the target is [WeakAxiomatic3]'s
    [srvwmo_consistent].

    THE THEOREM.  An RVWMO⁻-consistent graph that ALSO satisfies rule 14
    ("a memory event po-before a write is gmo-before it", [grule14]) is
    realized by a candidate — same image, same per-hart program rows, and
    THE SAME LOG: the candidate's final message list is exactly [gwrites G]
    (the graph's writes in gmo order) mapped through [gmsg].  So a graph
    read's per-byte [ts] entry, which names a gmo-WRITE-INDEX, is
    NUMERICALLY the candidate log position of the same write: the
    linearization renumbers nothing.

    THE CONSTRUCTION (closed form; no topological selection).  For an event
    [e], [gnxw G e] is the po-FIRST write at-or-after [e] in [e]'s own hart
    ([e] itself when [e] is a write).  The trace enumerates, in order:

      - for each write [w] of [gwrites G] (i.e. in gmo order): [w]'s
        SEGMENT — the events whose [gnxw] is [w], in po order.  Each
        segment lies in one hart and ends with [w] itself;
      - then, hart by hart, the TAILS: the events with no write at-or-after
        them.

    Both are read off one RANK function, [grank]: [gwix] of the next write,
    or [S |gwrites| + hart] when there is none.  The trace is
    [rblocks (grank G) (gevs G)] — the events grouped by rank, groups in
    rank order, each group in the source list's order.

    WHY IT WORKS.  Five placement facts, all [gpos]/[gwix] arithmetic:

    (P1) per-hart po order: hart [i]'s events appear in po order, so the
         per-agent label row is EQUAL to [gx_prog G !! i] ([lin_prog]) and
         candidate [po] IS graph [po] ([lin_po_order]);
    (P2) writes land at their [gwix] ([lin_ts_write]) — hence the same-log
         property and the verbatim reuse of [ts] entries;
    (P3) rf is gmo-FORWARD ([grf_gmo]: the [gpo] disjunct of [gvisible] is
         same-hart same-byte, so [gpoloc ⊆ gppo ⊆ gmo]), so a read's source
         is already in the prefix log ([lin_source_before]);
    (P4) po and rf both increase the trace index — (P1) and (P3);
    (P5) fr is [gpos]-forward ([gfr_ge]): a write the read did NOT take is
         not gmo-visible to it, and [gmo] is total on its members.

    THE OBLIGATIONS.  Only SIX are proved here: [cand_shape],
    [cand_values], [ax_coherence], [ax_atomicity], [ax_ord], [ax_rel_ord].
    The other five conjuncts of [axiomatic_ok] are free of [cand_values]
    ([WeakAxiomatic3] §12), and [ob]-acyclicity comes from
    [promise_free_ob_acyclic] once [promise_free_complete_local] has turned
    the six into [exec_wf] — the completeness theorem is the bootstrap.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations sorting.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2 WeakAxiomatic3
                            WeakRvwmoGraph.

(* ====================================================================== *)
(** * 1. A GENERIC ORDER-THEORY KIT

    Nothing here mentions the memory model: it is the list algebra the
    construction needs — grouping a list into rank blocks, and the two
    facts about [filter] (it preserves order, and a uniquely-satisfied
    predicate filters to a singleton). *)

(** ** 1.1 [pidx]: the position of an element in a list *)

Definition pidx {A} `{EqDecision A} (l : list A) (x : A) : nat :=
  match list_find (λ y, y = x) l with Some (i, _) => i | None => 0%nat end.

Lemma pidx_lookup {A} `{EqDecision A} (l : list A) x :
  x ∈ l → l !! pidx l x = Some x.
Proof.
  intros Hx. rewrite /pidx.
  destruct (list_find (λ y, y = x) l) as [[i z]|] eqn:Hf.
  - by apply list_find_Some in Hf as (Hi & -> & _).
  - destruct (list_find_elem_of (λ y, y = x) l x Hx eq_refl) as [? Hs].
    by rewrite Hf in Hs.
Qed.

Lemma pidx_of_lookup {A} `{EqDecision A} (l : list A) i x :
  NoDup l → l !! i = Some x → pidx l x = i.
Proof.
  intros Hnd Hi.
  apply (NoDup_lookup l (pidx l x) i x Hnd); [|done].
  by apply pidx_lookup, elem_of_list_lookup_2 with i.
Qed.

Lemma pidx_cons_eq {A} `{EqDecision A} (a : A) (l : list A) :
  pidx (a :: l) a = 0%nat.
Proof. rewrite /pidx /=. by rewrite decide_True. Qed.

Lemma pidx_cons_ne {A} `{EqDecision A} (a x : A) (l : list A) :
  x ≠ a → x ∈ l → pidx (a :: l) x = S (pidx l x).
Proof.
  intros Hne Hx. rewrite /pidx /=. rewrite decide_False; [done|].
  destruct (list_find (λ y, y = x) l) as [[i z]|] eqn:Hf; [done|].
  destruct (list_find_elem_of (λ y, y = x) l x Hx eq_refl) as [? Hs].
  by rewrite Hf in Hs.
Qed.

(** ** 1.2 Sortedness helpers (the [StronglySorted] ones live in
       [WeakRvwmoGraph] §6) *)

Lemma StronglySorted_weaken {A} (R1 R2 : relation A) (l : list A) :
  (∀ x y, x ∈ l → y ∈ l → R1 x y → R2 x y) →
  StronglySorted R1 l → StronglySorted R2 l.
Proof.
  intros Himp Hss. induction Hss as [|z l Hss IH Hall]; [constructor|].
  constructor.
  - apply IH. intros x y Hx Hy. apply Himp; by right.
  - apply Forall_lookup_2. intros i y Hy.
    apply Himp; [by left|by right; eapply elem_of_list_lookup_2, Hy|].
    by eapply Forall_lookup_1.
Qed.

(** FILTER PRESERVES RELATIVE ORDER, in the form the trace uses: the
    filtered list is sorted by position in the ORIGINAL list. *)
Lemma filter_sorted_pidx {A} `{EqDecision A} (P : A → Prop)
    `{∀ x, Decision (P x)} (l : list A) :
  NoDup l → StronglySorted (λ x y, (pidx l x < pidx l y)%nat) (filter P l).
Proof.
  induction l as [|a l IH]; intros Hnd; [rewrite filter_nil; constructor|].
  pose proof (NoDup_cons_1_1 _ _ Hnd) as Ha. apply NoDup_cons_1_2 in Hnd.
  assert (Hsub : ∀ x, x ∈ filter P l → pidx (a :: l) x = S (pidx l x)).
  { intros x Hx. apply elem_of_list_filter in Hx as [_ Hx].
    apply pidx_cons_ne; [|done]. intros ->. done. }
  rewrite filter_cons. case_decide as HPa.
  - constructor.
    + eapply StronglySorted_weaken; [|by apply IH].
      intros x y Hx Hy Hxy. cbn in Hxy. rewrite (Hsub x Hx) (Hsub y Hy). lia.
    + apply Forall_lookup_2. intros i y Hy.
      pose proof (elem_of_list_lookup_2 _ _ _ Hy) as Hy'.
      rewrite pidx_cons_eq (Hsub y Hy'). lia.
  - eapply StronglySorted_weaken; [|by apply IH].
    intros x y Hx Hy Hxy. cbn in Hxy. rewrite (Hsub x Hx) (Hsub y Hy). lia.
Qed.

(** ** 1.3 [filter]: emptiness and uniqueness *)

Lemma filter_no {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  (∀ x, x ∈ l → ¬ P x) → filter P l = [].
Proof.
  induction l as [|a l IH]; [done|]. intros H0.
  rewrite filter_cons. case_decide as Ha.
  { exfalso. apply (H0 a); [by left|done]. }
  apply IH. intros x Hx. apply H0. by right.
Qed.

Lemma filter_unique {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) x :
  NoDup l → x ∈ l → P x → (∀ y, y ∈ l → P y → y = x) → filter P l = [x].
Proof.
  intros Hnd. revert x. induction l as [|a l IH]; intros x Hx HP Huniq.
  { by apply elem_of_nil in Hx. }
  pose proof (NoDup_cons_1_1 _ _ Hnd) as Ha. apply NoDup_cons_1_2 in Hnd.
  rewrite filter_cons. case_decide as HPa.
  - assert (a = x) as ->.
    { apply Huniq; [by left|done]. }
    f_equal. apply filter_no. intros y Hy HPy.
    assert (y = x) as ->; [apply Huniq; [by right|done]|done].
  - apply elem_of_cons in Hx as [->|Hx]; [done|].
    apply IH; [done|done|done|]. intros y Hy HPy. apply Huniq; [by right|done].
Qed.

(** ** 1.4 [mjoin] over an index range *)

Lemma elem_of_mjoin_seq {A} (f : nat → list A) N x :
  x ∈ mjoin (f <$> seq 0 N) ↔ ∃ j, (j < N)%nat ∧ x ∈ f j.
Proof.
  rewrite elem_of_list_join. split.
  - intros (l & Hx & Hl). apply elem_of_list_fmap in Hl as (j & -> & Hj).
    apply elem_of_seq in Hj. exists j. split; [lia|done].
  - intros (j & Hj & Hx). exists (f j). split; [done|].
    apply elem_of_list_fmap. exists j. split; [done|]. apply elem_of_seq. lia.
Qed.

Lemma mjoin_seq_S {A} (f : nat → list A) N :
  mjoin (f <$> seq 0 (S N)) = mjoin (f <$> seq 0 N) ++ f N.
Proof.
  rewrite seq_S fmap_app join_app /=. by rewrite app_nil_r.
Qed.

Lemma mjoin_seq_none {A} (f : nat → list A) N :
  (∀ j, (j < N)%nat → f j = []) → mjoin (f <$> seq 0 N) = [].
Proof.
  induction N as [|N IH]; intros H0; [done|].
  rewrite mjoin_seq_S. assert (Hz : f N = []) by (apply H0; lia).
  rewrite Hz app_nil_r.
  apply IH. intros j Hj. apply H0. lia.
Qed.

Lemma mjoin_seq_single {A} (f : nat → list A) N i :
  (∀ j, (j < N)%nat → j ≠ i → f j = []) → (i < N)%nat →
  mjoin (f <$> seq 0 N) = f i.
Proof.
  induction N as [|N IH]; intros H0 Hi; [lia|].
  rewrite mjoin_seq_S.
  destruct (decide (i = N)) as [->|Hne].
  - assert (Hz : mjoin (f <$> seq 0 N) = []).
    { apply mjoin_seq_none. intros j Hj. apply H0; lia. }
    by rewrite Hz.
  - assert (Hz : f N = []) by (apply H0; lia).
    rewrite Hz app_nil_r.
    apply IH; [intros j Hj Hj'; apply H0; lia|lia].
Qed.

Lemma filter_mjoin_fmap {A B} (P : A → Prop) `{∀ x, Decision (P x)}
    (f : B → list A) (l : list B) :
  filter P (mjoin (f <$> l)) = mjoin ((λ j, filter P (f j)) <$> l).
Proof. induction l as [|b l IH]; [done|]. by rewrite /= list_basics.filter_app IH. Qed.

Lemma nodup_mjoin_seq {A} (f : nat → list A) (key : A → nat) N :
  (∀ j, NoDup (f j)) → (∀ j x, x ∈ f j → key x = j) →
  NoDup (mjoin (f <$> seq 0 N)).
Proof.
  intros Hnd Hkey. induction N as [|N IH]; [constructor|].
  rewrite mjoin_seq_S. rewrite list_relations.NoDup_app. split_and!; [exact IH| |apply Hnd].
  intros x Hx Hx2. apply elem_of_mjoin_seq in Hx as (j & Hj & Hxj).
  pose proof (Hkey j x Hxj) as E1. pose proof (Hkey N x Hx2) as E2. lia.
Qed.

(** ** 1.5 [rblocks]: group a list by a rank, blocks in rank order *)

Definition rblocks {A} (rk : A → nat) (l : list A) (n : nat) : list A :=
  mjoin ((λ d, filter (λ x, rk x = d) l) <$> seq 0 n).

Lemma rblocks_S {A} (rk : A → nat) (l : list A) n :
  rblocks rk l (S n) = rblocks rk l n ++ filter (λ x, rk x = n) l.
Proof.
  rewrite /rblocks.
  exact (mjoin_seq_S (λ d, filter (λ x, rk x = d) l) n).
Qed.

Lemma elem_of_rblocks {A} (rk : A → nat) (l : list A) n x :
  x ∈ rblocks rk l n ↔ x ∈ l ∧ (rk x < n)%nat.
Proof.
  rewrite /rblocks elem_of_mjoin_seq. split.
  - intros (d & Hd & Hx). apply elem_of_list_filter in Hx as [<- Hx].
    split; [done|lia].
  - intros [Hx Hrk]. exists (rk x). split; [lia|]. by apply elem_of_list_filter.
Qed.

Lemma rblocks_nodup {A} (rk : A → nat) (l : list A) n :
  NoDup l → NoDup (rblocks rk l n).
Proof.
  intros Hnd. induction n as [|n IH]; [constructor|].
  rewrite rblocks_S. rewrite list_relations.NoDup_app. split_and!.
  - exact IH.
  - intros x Hx Hx2. apply elem_of_rblocks in Hx as [_ Hlt].
    apply elem_of_list_filter in Hx2 as [Heq _]. lia.
  - by apply list_relations.NoDup_filter.
Qed.

(** The blocks are constant-rank and in rank order — no hypothesis at all. *)
Lemma rblocks_rank_sorted {A} (rk : A → nat) (l : list A) n :
  StronglySorted (λ x y, (rk x ≤ rk y)%nat) (rblocks rk l n).
Proof.
  induction n as [|n IH]; [constructor|].
  rewrite rblocks_S. apply StronglySorted_app_2.
  - intros x y Hx Hy. apply elem_of_rblocks in Hx as [_ Hlt].
    apply elem_of_list_filter in Hy as [Heq _]. lia.
  - exact IH.
  - apply StronglySorted_lookup_intro. intros i j x y Hi Hj _.
    pose proof (elem_of_list_lookup_2 _ _ _ Hi) as Hi'.
    pose proof (elem_of_list_lookup_2 _ _ _ Hj) as Hj'.
    apply elem_of_list_filter in Hi' as [Hx _].
    apply elem_of_list_filter in Hj' as [Hy _]. lia.
Qed.

Lemma rblocks_sorted {A} (rk : A → nat) (R : relation A) (l : list A) n :
  StronglySorted R l →
  (∀ x y, x ∈ l → y ∈ l → (rk x < rk y)%nat → R x y) →
  StronglySorted R (rblocks rk l n).
Proof.
  intros Hss Hcross. induction n as [|n IH]; [constructor|].
  rewrite rblocks_S. apply StronglySorted_app_2.
  - intros x y Hx Hy. apply elem_of_rblocks in Hx as [Hxl Hlt].
    apply elem_of_list_filter in Hy as [Heq Hyl]. apply Hcross; [done|done|lia].
  - exact IH.
  - by apply StronglySorted_filter.
Qed.

Lemma rblocks_perm {A} (rk : A → nat) (l : list A) n :
  NoDup l → (∀ x, x ∈ l → (rk x < n)%nat) → rblocks rk l n ≡ₚ l.
Proof.
  intros Hnd Hb. apply list_relations.NoDup_Permutation; [by apply rblocks_nodup|done|].
  intros x. rewrite elem_of_rblocks. naive_solver.
Qed.

(** A list already sorted by rank (with a tie-break the rank refines) is its
    own block decomposition. *)
Lemma rblocks_id {A} (rk : A → nat) (R : relation A) (l : list A) n :
  NoDup l → StronglySorted R l →
  (∀ x, x ∈ l → (rk x < n)%nat) →
  (∀ x y, x ∈ l → y ∈ l → (rk x < rk y)%nat → R x y) →
  (∀ x y, x ∈ l → y ∈ l → R x y → R y x → x = y) →
  rblocks rk l n = l.
Proof.
  intros Hnd Hss Hb Hcross Hasym.
  apply (StronglySorted_unique_strong R).
  - intros x y Hx Hy Hxy Hyx.
    apply elem_of_rblocks in Hx as [Hx _]. by apply Hasym.
  - by apply rblocks_sorted.
  - exact Hss.
  - by apply rblocks_perm.
Qed.

Lemma rblocks_ext {A} (rk : A → nat) (l l' : list A) n :
  (∀ d, filter (λ x, rk x = d) l = filter (λ x, rk x = d) l') →
  rblocks rk l n = rblocks rk l' n.
Proof.
  intros H. rewrite /rblocks. f_equal.
  induction (seq 0 n) as [|d ds IH]; [done|].
  rewrite !fmap_cons. f_equal; [apply H|exact IH].
Qed.

Lemma rblocks_filter {A} (rk : A → nat) (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) n :
  filter P (rblocks rk l n) = rblocks rk (filter P l) n.
Proof.
  rewrite /rblocks filter_mjoin_fmap. f_equal.
  induction (seq 0 n) as [|d ds IH]; [done|].
  rewrite !fmap_cons. f_equal; [|exact IH].
  rewrite !list_filter_filter. apply list_filter_iff. tauto.
Qed.

(* ====================================================================== *)
(** * 2. THE CONSTRUCTION *)

(** The program row of a hart ([] outside the program). *)
Definition grow (G : gexec) (i : agent) : list lbl := default [] (gx_prog G !! i).

(** The labeled events of one hart, in po order; and of the whole graph. *)
Definition gevs_hart (G : gexec) (i : agent) : list geid :=
  (λ k, (i, k)) <$> seq 0 (length (grow G i)).

Definition gevs (G : gexec) : list geid :=
  mjoin (gevs_hart G <$> seq 0 (length (gx_prog G))).

(** The po-FIRST write at-or-after [e], in [e]'s own hart ([e] itself when
    [e] is a write). *)
Definition gnxw (G : gexec) (e : geid) : option geid :=
  (λ ik : nat * nat, (e.1, ik.2)) <$>
    list_find (λ k, gis_w G (e.1, k) = true)
              (seq e.2 (length (grow G e.1) - e.2)).

(** THE RANK.  [gwix] of the next write — so segments come out in gmo order
    and each segment ends with its own write — or a past-the-end slot
    indexed by the hart, for the tails. *)
Definition grank (G : gexec) (e : geid) : nat :=
  match gnxw G e with
  | Some w => gwix G w
  | None => (S (length (gwrites G)) + e.1)%nat
  end.

Definition grank_bound (G : gexec) : nat :=
  (S (length (gwrites G)) + length (gx_prog G))%nat.

Definition glin_eids (G : gexec) : list geid :=
  rblocks (grank G) (gevs G) (grank_bound G).

Definition glbl (G : gexec) (e : geid) : lbl :=
  default (LFence false false false false) (gx_lbl G e).

Definition glin_step (G : gexec) (e : geid) : estep := EStep e.1 (glbl G e).

(** The message an event contributes to the log. *)
Definition gmsg (G : gexec) (e : geid) : option wmsg :=
  match gx_lbl G e with
  | Some l =>
      match lb_wr l with
      | Some (base, vs) => Some (WMsg base vs (Some e.1) (lb_cls l))
      | None => None
      end
  | None => None
  end.

Definition lin_cand (G : gexec) : cand :=
  Cand (gx_img G) (glin_step G <$> glin_eids G).

(** How many messages the first [k] steps append. *)
Definition lin_nw (G : gexec) (k : nat) : nat :=
  length (filter (gis_w G) (take k (glin_eids G))).

(* ---------------------------------------------------------------------- *)
(** ** 2.1 Events and labels — hypothesis-free bookkeeping *)

Lemma grow_lookup G i :
  (i < length (gx_prog G))%nat → gx_prog G !! i = Some (grow G i).
Proof.
  intros Hi. rewrite /grow.
  destruct (gx_prog G !! i) as [p|] eqn:Hp; [done|].
  apply lookup_ge_None in Hp. lia.
Qed.

Lemma gx_lbl_bounds G e :
  is_Some (gx_lbl G e) ↔
  ((e.1 < length (gx_prog G))%nat ∧ (e.2 < length (grow G e.1))%nat).
Proof.
  rewrite /gx_lbl. split.
  - intros [l Hl]. destruct (gx_prog G !! e.1) as [p|] eqn:Hp; [|done].
    simpl in Hl. assert (Hg : grow G e.1 = p) by (rewrite /grow Hp //).
    split; [by eapply lookup_lt_Some|]. rewrite Hg. by eapply lookup_lt_Some.
  - intros [Hi Hk]. rewrite (grow_lookup G e.1 Hi) /=.
    by apply lookup_lt_is_Some_2.
Qed.

Lemma glbl_some G i k :
  (i < length (gx_prog G))%nat → (k < length (grow G i))%nat →
  is_Some (gx_lbl G (i, k)).
Proof. intros ??. by apply gx_lbl_bounds. Qed.

Lemma elem_of_gevs_hart G i e :
  e ∈ gevs_hart G i ↔ (e.1 = i ∧ (e.2 < length (grow G i))%nat).
Proof.
  rewrite /gevs_hart elem_of_list_fmap. split.
  - intros (k & -> & Hk). apply elem_of_seq in Hk. simpl. split; [done|lia].
  - intros [Hi Hk]. exists e.2. split.
    + destruct e as [i' k']; simpl in *; by subst.
    + apply elem_of_seq. lia.
Qed.

Lemma gevs_hart_lookup G i k :
  (k < length (grow G i))%nat → gevs_hart G i !! k = Some (i, k).
Proof.
  intros Hk. rewrite /gevs_hart list_lookup_fmap.
  by rewrite (lookup_seq_lt 0 (length (grow G i)) k Hk).
Qed.

Lemma gevs_hart_lookup_inv G i k e :
  gevs_hart G i !! k = Some e → e = (i, k) ∧ (k < length (grow G i))%nat.
Proof.
  rewrite /gevs_hart list_lookup_fmap.
  destruct (seq 0 (length (grow G i)) !! k) as [x|] eqn:Hs; simpl; [|done].
  apply lookup_seq in Hs as [-> Hlt]. intros Heq; simplify_eq. done.
Qed.

Lemma gevs_hart_nodup G i : NoDup (gevs_hart G i).
Proof.
  apply NoDup_alt. intros a b e Ha Hb.
  apply gevs_hart_lookup_inv in Ha as [-> _].
  apply gevs_hart_lookup_inv in Hb as [Heq _]. by simplify_eq.
Qed.

Lemma elem_of_gevs G e : e ∈ gevs G ↔ is_Some (gx_lbl G e).
Proof.
  rewrite /gevs elem_of_mjoin_seq. split.
  - intros (j & Hj & He). apply elem_of_gevs_hart in He as [He Hk].
    subst j. apply gx_lbl_bounds. by split.
  - intros He. apply gx_lbl_bounds in He as [Hi Hk].
    exists e.1. split; [done|]. by apply elem_of_gevs_hart.
Qed.

Lemma gevs_nodup G : NoDup (gevs G).
Proof.
  apply (nodup_mjoin_seq _ (λ e : geid, e.1)).
  - apply gevs_hart_nodup.
  - intros j e He. by apply elem_of_gevs_hart in He as [-> _].
Qed.

Lemma filter_all {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  (∀ x, x ∈ l → P x) → filter P l = l.
Proof.
  induction l as [|a l IH]; [done|]. intros H0.
  rewrite filter_cons. case_decide as Ha.
  - f_equal. apply IH. intros x Hx. apply H0. by right.
  - exfalso. apply Ha, H0. by left.
Qed.

Lemma filter_gevs_hart G i :
  filter (λ e : geid, e.1 = i) (gevs G) = gevs_hart G i.
Proof.
  rewrite /gevs filter_mjoin_fmap.
  destruct (decide (i < length (gx_prog G))%nat) as [Hi|Hi].
  - assert (Hone : mjoin ((λ j, filter (λ e : geid, e.1 = i) (gevs_hart G j))
                            <$> seq 0 (length (gx_prog G)))
                   = filter (λ e : geid, e.1 = i) (gevs_hart G i)).
    { apply (mjoin_seq_single
               (λ j, filter (λ e : geid, e.1 = i) (gevs_hart G j))
               (length (gx_prog G)) i); [|done].
      intros j Hj Hne. apply filter_no. intros e He Hc.
      apply elem_of_gevs_hart in He as [He1 _]. apply Hne. by rewrite -He1. }
    rewrite Hone. apply filter_all.
    intros e He. by apply elem_of_gevs_hart in He as [He1 _].
  - assert (Hnil : gevs_hart G i = []).
    { rewrite /gevs_hart /grow.
      destruct (gx_prog G !! i) as [p|] eqn:Hp; [|done].
      exfalso. apply lookup_lt_Some in Hp. lia. }
    rewrite Hnil. apply mjoin_seq_none. intros j Hj.
    apply filter_no. intros e He Hc.
    apply elem_of_gevs_hart in He as [He1 _]. rewrite He1 in Hc. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 2.2 [gnxw]: the next write *)

Lemma gnxw_Some G i k w :
  gnxw G (i, k) = Some w →
  ∃ m, w = (i, m) ∧ (k ≤ m)%nat ∧ (m < length (grow G i))%nat ∧
       gis_w G (i, m) = true ∧
       (∀ k', (k ≤ k')%nat → (k' < m)%nat → gis_w G (i, k') = false).
Proof.
  rewrite /gnxw /=.
  destruct (list_find _ _) as [[n j]|] eqn:Hf; [|done].
  intros Heq; simplify_eq/=.
  apply list_find_Some in Hf as (Hn & Hw & Hmin).
  apply lookup_seq in Hn as [-> Hlt].
  exists (k + n)%nat. split_and!; [done|lia|lia|done|].
  intros k' Hk1 Hk2. apply not_true_is_false. intros Hw'.
  apply (Hmin (k' - k)%nat k'); [|lia|done].
  apply lookup_seq. split; lia.
Qed.

Lemma gnxw_None G i k k' :
  gnxw G (i, k) = None → (k ≤ k')%nat → (k' < length (grow G i))%nat →
  gis_w G (i, k') = false.
Proof.
  rewrite /gnxw /=. destruct (list_find _ _) as [[n j]|] eqn:Hf; [done|].
  intros _ Hk1 Hk2. apply not_true_is_false. intros Hw.
  destruct (list_find_elem_of (λ k0, gis_w G (i, k0) = true)
              (seq k (length (grow G i) - k)) k'
              ltac:(apply elem_of_seq; lia) Hw) as [? Hs].
  by rewrite Hf in Hs.
Qed.

Lemma gnxw_self G i k :
  is_Some (gx_lbl G (i, k)) → gis_w G (i, k) = true →
  gnxw G (i, k) = Some (i, k).
Proof.
  intros Hl Hw. apply gx_lbl_bounds in Hl as [Hi Hk]. simpl in Hi, Hk.
  destruct (gnxw G (i, k)) as [w|] eqn:Hf; last first.
  { by rewrite (gnxw_None G i k k Hf ltac:(lia) Hk) in Hw. }
  destruct (gnxw_Some G i k w Hf) as (m & -> & Hkm & Hm & Hwm & Hmin).
  destruct (decide (k = m)) as [->|Hne]; [done|].
  by rewrite (Hmin k ltac:(lia) ltac:(lia)) in Hw.
Qed.

(* ====================================================================== *)
(** * 3. THE GRAPH-SIDE FACTS AND THE TRACE ORDER

    Everything below runs under RVWMO⁻ + rule 14; the section variables ARE
    [rvwmo_minus_consistent G ∧ grule14 G], unpacked. *)

Section lin.
Context (G : gexec).
Context (Hwf : gwf G) (Hppo : gppo_gmo G).
Context (Hlv : gload_value G) (Hat : gatomicity G) (H14 : grule14 G).

Local Lemma Hnd : NoDup (gx_gmo G).
Proof. apply Hwf. Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.1 Membership and classification *)

Lemma gis_w_gmem e : is_Some (gx_lbl G e) → gis_w G e = true → gmem G e.
Proof.
  intros [l Hl] Hw. exists l. split; [done|].
  rewrite /gis_w Hl in Hw. rewrite /lb_is_mem Hw orb_true_r //.
Qed.

Lemma gis_w_glbl_is e :
  is_Some (gx_lbl G e) → gis_w G e = true → glbl_is G e lb_is_w.
Proof. intros [l Hl] Hw. exists l. rewrite /gis_w Hl in Hw. by split. Qed.

Lemma gwrites_byte_gw e a v : gwrites_byte G e a v → e ∈ gwrites G.
Proof.
  intros (l & base & vs & j & Hl & Hwr & _).
  apply gwrites_elem_of. assert (Hw : gis_w G e = true).
  { rewrite /gis_w Hl. by eapply lb_wr_is_w. }
  split; [|done]. apply (gwf_mem_gmo G e Hwf), gis_w_gmem; [by eexists|done].
Qed.

Lemma gwrites_byte_lbl e a v : gwrites_byte G e a v → is_Some (gx_lbl G e).
Proof. intros (l & base & vs & j & Hl & _). by eexists. Qed.

Lemma gwrites_byte_isw e a v : gwrites_byte G e a v → gis_w G e = true.
Proof.
  intros (l & base & vs & j & Hl & Hwr & _). rewrite /gis_w Hl.
  by eapply lb_wr_is_w.
Qed.

Lemma greads_byte_lbl e a t v : greads_byte G e a t v → is_Some (gx_lbl G e).
Proof. intros (l & base & ts & vs & j & Hl & _). by eexists. Qed.

Lemma greads_byte_mem e a t v : greads_byte G e a t v → e ∈ gx_gmo G.
Proof.
  intros (l & base & ts & vs & j & Hl & Hrd & _).
  apply (gwf_mem_gmo G e Hwf). exists l. split; [done|].
  rewrite /lb_is_mem (lb_rd_is_r l _ Hrd) //.
Qed.

Lemma gwrites_gmo w : w ∈ gwrites G → w ∈ gx_gmo G.
Proof. intros H. by apply gwrites_elem_of in H as [? _]. Qed.

Lemma gwrites_lbl w : w ∈ gwrites G → is_Some (gx_lbl G w).
Proof.
  intros H. apply gwrites_gmo, (gwf_gmo_mem G w Hwf) in H as (l & Hl & _).
  by eexists.
Qed.

Lemma gwrites_isw w : w ∈ gwrites G → gis_w G w = true.
Proof. intros H. by apply gwrites_elem_of in H as [_ ?]. Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.2 (P3) rf is gmo-FORWARD, and (P5) fr is gpos-forward *)

Lemma gcomax r a t v w' v' :
  greads_byte G r a t v → gwrites_byte G w' a v' → gvisible G w' r →
  (gwix G w' ≤ t)%nat.
Proof. intros Hrd Hwr Hvis. by eapply (proj2 (Hlv r a t v Hrd)). Qed.

(** THE KEY (P3): a read's named source is gmo-BEFORE it.  The [gpo]
    disjunct of [gvisible] (store forwarding) is same-hart AND same-byte, so
    ppo rules 1–3 turn it into a gmo edge. *)
Lemma grf_gmo r a i v w :
  greads_byte G r a (S i) v → gwrite_at G (S i) = Some w → gmo_lt G w r.
Proof.
  intros Hrd Hw.
  destruct (proj1 (Hlv r a (S i) v Hrd)) as (w0 & Hw0 & Hwb & Hvis).
  rewrite Hw in Hw0. simplify_eq.
  destruct Hvis as [Hmo|Hpo]; [exact Hmo|].
  apply Hppo. left. split; [exact Hpo|]. exists a. split.
  - left. by eexists.
  - right. by exists (S i), v.
Qed.

(** (P5): a write the read did NOT take is not gmo-visible to it, and [gmo]
    is total on members. *)
Lemma gfr_ge r a t v w' v' :
  greads_byte G r a t v → gwrites_byte G w' a v' → (t < gwix G w')%nat →
  (gpos G r ≤ gpos G w')%nat.
Proof.
  intros Hrd Hwr Hlt.
  apply (gmo_nlt_ge G w' r Hnd (gwrites_gmo w' (gwrites_byte_gw w' a v' Hwr))
                    (greads_byte_mem r a t v Hrd)).
  intros Hmo. pose proof (gcomax r a t v w' v' Hrd Hwr (or_introl Hmo)). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.3 Same-hart writes: position order IS [gwix] order (rule 14) *)

Lemma gsame_hart_gwix i k1 k2 :
  (i < length (gx_prog G))%nat →
  (k1 < length (grow G i))%nat → (k2 < length (grow G i))%nat →
  gis_w G (i, k1) = true → gis_w G (i, k2) = true → (k1 < k2)%nat →
  (gwix G (i, k1) < gwix G (i, k2))%nat.
Proof.
  intros Hi Hb1 Hb2 Hw1 Hw2 Hlt.
  assert (Hl1 : is_Some (gx_lbl G (i, k1))) by by apply glbl_some.
  assert (Hl2 : is_Some (gx_lbl G (i, k2))) by by apply glbl_some.
  assert (Hmo : gmo_lt G (i, k1) (i, k2)).
  { apply H14; [|by apply gis_w_gmem|by apply gis_w_glbl_is].
    split_and!; simpl; [done|lia|done|done]. }
  apply (gwix_gpos_lt G (i, k1) (i, k2) Hnd
           (gis_w_gwrites G (i, k1) Hwf Hl1 Hw1)
           (gis_w_gwrites G (i, k2) Hwf Hl2 Hw2)).
  by apply Hmo.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.4 The rank: monotone in po, bounded, and [gwix] on writes *)

Lemma grank_write e : e ∈ gwrites G → grank G e = gwix G e.
Proof.
  intros He. rewrite /grank. destruct e as [i k].
  by rewrite (gnxw_self G i k (gwrites_lbl _ He) (gwrites_isw _ He)).
Qed.

Lemma grank_lt_bound e : is_Some (gx_lbl G e) → (grank G e < grank_bound G)%nat.
Proof.
  intros Hl. pose proof Hl as Hl'. apply gx_lbl_bounds in Hl' as [Hi Hk].
  rewrite /grank /grank_bound. destruct e as [i k]; simpl in Hi, Hk.
  destruct (gnxw G (i, k)) as [w|] eqn:Hf; [|simpl; lia].
  destruct (gnxw_Some G i k w Hf) as (m & -> & _ & Hm & Hw & _).
  pose proof (gwix_le G (i, m)
                (gis_w_gwrites G (i, m) Hwf (glbl_some G i m Hi Hm) Hw)). lia.
Qed.

Lemma grank_mono i k1 k2 :
  (i < length (gx_prog G))%nat → (k1 ≤ k2)%nat →
  (k2 < length (grow G i))%nat →
  (grank G (i, k1) ≤ grank G (i, k2))%nat.
Proof.
  intros Hi Hle Hk2. rewrite /grank.
  destruct (gnxw G (i, k2)) as [w2|] eqn:H2.
  - destruct (gnxw_Some G i k2 w2 H2) as (m2 & -> & Hk2m & Hm2 & Hw2 & _).
    destruct (gnxw G (i, k1)) as [w1|] eqn:H1; last first.
    { by rewrite (gnxw_None G i k1 m2 H1 ltac:(lia) Hm2) in Hw2. }
    destruct (gnxw_Some G i k1 w1 H1) as (m1 & -> & Hk1m & Hm1 & Hw1 & Hmin1).
    assert (Hle' : (m1 ≤ m2)%nat).
    { destruct (decide (m2 < m1)%nat) as [Hlt|]; [|lia].
      by rewrite (Hmin1 m2 ltac:(lia) Hlt) in Hw2. }
    destruct (decide (m1 = m2)) as [->|Hne]; [simpl; lia|].
    apply Nat.lt_le_incl. apply gsame_hart_gwix; [done|done|done|done|done|lia].
  - destruct (gnxw G (i, k1)) as [w1|] eqn:H1; [|simpl; lia].
    destruct (gnxw_Some G i k1 w1 H1) as (m1 & -> & _ & Hm1 & Hw1 & _).
    pose proof (gwix_le G (i, m1)
                  (gis_w_gwrites G (i, m1) Hwf (glbl_some G i m1 Hi Hm1) Hw1)).
    lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.5 The trace: NoDup, membership, and the two order facts *)

Lemma glin_nodup : NoDup (glin_eids G).
Proof. apply rblocks_nodup, gevs_nodup. Qed.

Lemma elem_of_glin e : e ∈ glin_eids G ↔ is_Some (gx_lbl G e).
Proof.
  rewrite /glin_eids elem_of_rblocks elem_of_gevs. split.
  - by intros [? _].
  - intros He. split; [done|by apply grank_lt_bound].
Qed.

Lemma glin_lookup_lbl k e : glin_eids G !! k = Some e → is_Some (gx_lbl G e).
Proof. intros H. apply elem_of_glin. by eapply elem_of_list_lookup_2. Qed.

Lemma glin_index e : is_Some (gx_lbl G e) → ∃ k, glin_eids G !! k = Some e.
Proof. intros H. apply elem_of_list_lookup_1. by apply elem_of_glin. Qed.

(** (P1) The per-hart subsequence of the trace IS the hart's event row. *)
Lemma glin_hart i : filter (λ e : geid, e.1 = i) (glin_eids G) = gevs_hart G i.
Proof.
  rewrite /glin_eids rblocks_filter filter_gevs_hart.
  destruct (decide (i < length (gx_prog G))%nat) as [Hi|Hi]; last first.
  { assert (Hnil : gevs_hart G i = []).
    { rewrite /gevs_hart /grow.
      destruct (gx_prog G !! i) as [p|] eqn:Hp; [|done].
      exfalso. apply lookup_lt_Some in Hp. lia. }
    rewrite Hnil /rblocks.
    apply (mjoin_seq_none (λ d, filter (λ x : geid, grank G x = d) [])
                          (grank_bound G)).
    intros j _. done. }
  apply (rblocks_id (grank G) (λ x y : geid, (x.2 ≤ y.2)%nat)).
  - apply gevs_hart_nodup.
  - apply StronglySorted_lookup_intro. intros a b x y Hx Hy Hab.
    apply gevs_hart_lookup_inv in Hx as [-> _].
    apply gevs_hart_lookup_inv in Hy as [-> _]. simpl. lia.
  - intros x Hx. apply grank_lt_bound, gx_lbl_bounds.
    apply elem_of_gevs_hart in Hx as [Hx1 Hx2]. rewrite Hx1. by split.
  - intros x y Hx Hy Hrk.
    apply elem_of_gevs_hart in Hx as [Hx1 Hx2].
    apply elem_of_gevs_hart in Hy as [Hy1 Hy2].
    destruct (decide (x.2 ≤ y.2)%nat) as [?|Hgt]; [done|exfalso].
    destruct x as [ix kx], y as [iy ky]; simpl in *; subst ix iy.
    pose proof (grank_mono i ky kx Hi ltac:(lia) Hx2). lia.
  - intros x y Hx Hy H1 H2.
    apply elem_of_gevs_hart in Hx as [Hx1 _].
    apply elem_of_gevs_hart in Hy as [Hy1 _].
    destruct x as [ix kx], y as [iy ky]; simpl in *; subst ix iy.
    f_equal; lia.
Qed.

(** ... hence trace order and po order agree inside a hart. *)
Lemma glin_po_lt k1 k2 e1 e2 :
  glin_eids G !! k1 = Some e1 → glin_eids G !! k2 = Some e2 →
  e1.1 = e2.1 → (e1.2 < e2.2)%nat → (k1 < k2)%nat.
Proof.
  intros H1 H2 Hag Hlt.
  pose proof (filter_sorted_pidx (λ e : geid, e.1 = e1.1) (glin_eids G)
                glin_nodup) as Hss.
  rewrite (glin_hart e1.1) in Hss.
  assert (Hb1 : (e1.2 < length (grow G e1.1))%nat).
  { by apply gx_lbl_bounds, (glin_lookup_lbl k1). }
  assert (Hb2 : (e2.2 < length (grow G e1.1))%nat).
  { rewrite Hag. by apply gx_lbl_bounds, (glin_lookup_lbl k2). }
  assert (Hg1 : gevs_hart G e1.1 !! e1.2 = Some e1).
  { rewrite (gevs_hart_lookup G e1.1 e1.2 Hb1). by destruct e1. }
  assert (Hg2 : gevs_hart G e1.1 !! e2.2 = Some e2).
  { rewrite (gevs_hart_lookup G e1.1 e2.2 Hb2). destruct e2; simpl in *.
    by rewrite Hag. }
  pose proof (StronglySorted_lookup_elim _ _ e1.2 e2.2 e1 e2 Hss Hg1 Hg2 Hlt)
    as Hp. cbn in Hp.
  rewrite (pidx_of_lookup (glin_eids G) k1 e1 glin_nodup H1) in Hp.
  rewrite (pidx_of_lookup (glin_eids G) k2 e2 glin_nodup H2) in Hp.
  exact Hp.
Qed.

Lemma glin_po_iff k1 k2 e1 e2 :
  glin_eids G !! k1 = Some e1 → glin_eids G !! k2 = Some e2 → e1.1 = e2.1 →
  ((k1 < k2)%nat ↔ (e1.2 < e2.2)%nat).
Proof.
  intros H1 H2 Hag. split; [|by eapply glin_po_lt].
  intros Hk. destruct (decide (e1.2 < e2.2)%nat) as [?|Hge]; [done|exfalso].
  destruct (decide (e1.2 = e2.2)) as [Heq|Hne].
  - assert (e1 = e2) as ->.
    { destruct e1, e2; simpl in *; by simplify_eq. }
    assert (k1 = k2) as -> by (by eapply NoDup_lookup; [apply glin_nodup| |]).
    lia.
  - pose proof (glin_po_lt k2 k1 e2 e1 H2 H1 ltac:(done) ltac:(lia)). lia.
Qed.

(** Rank order implies trace order — the blocks are emitted in rank order. *)
Lemma glin_rank_lt k1 k2 e1 e2 :
  glin_eids G !! k1 = Some e1 → glin_eids G !! k2 = Some e2 →
  (grank G e1 < grank G e2)%nat → (k1 < k2)%nat.
Proof.
  intros H1 H2 Hlt.
  pose proof (rblocks_rank_sorted (grank G) (gevs G) (grank_bound G)) as Hss.
  destruct (decide (k1 < k2)%nat) as [?|Hge]; [done|exfalso].
  destruct (decide (k1 = k2)) as [->|Hne].
  { rewrite H1 in H2. simplify_eq. lia. }
  pose proof (StronglySorted_lookup_elim _ _ k2 k1 e2 e1 Hss H2 H1
                ltac:(lia)) as Hx. cbn in Hx. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.6 (P2) The trace's writes ARE [gwrites G] *)

Lemma glin_writes : filter (gis_w G) (glin_eids G) = gwrites G.
Proof.
  assert (Hel : ∀ e, e ∈ filter (gis_w G) (gevs G) ↔ e ∈ gwrites G).
  { intros e. split.
    - intros He. apply elem_of_list_filter in He as [Hb He].
      apply Is_true_true_1 in Hb.
      apply (gis_w_gwrites G e Hwf); [by apply elem_of_gevs|done].
    - intros He. apply elem_of_list_filter. split.
      + by apply Is_true_true_2, gwrites_isw.
      + by apply elem_of_gevs, gwrites_lbl. }
  rewrite /glin_eids rblocks_filter.
  transitivity (rblocks (grank G) (gwrites G) (grank_bound G)); last first.
  { apply (rblocks_id (grank G) (λ x y : geid, (gwix G x ≤ gwix G y)%nat)).
    - apply (gwrites_nodup G Hnd).
    - eapply StronglySorted_weaken; [|apply (gwrites_sorted G Hnd)].
      intros x y Hx Hy Hxy. cbn in Hxy.
      apply Nat.lt_le_incl, (gwix_gpos_lt G x y Hnd Hx Hy). exact Hxy.
    - intros x Hx. by apply grank_lt_bound, gwrites_lbl.
    - intros x y Hx Hy Hrk. rewrite (grank_write x Hx) (grank_write y Hy) in Hrk.
      lia.
    - intros x y Hx Hy H1 H2. cbn in H1, H2.
      apply (gwix_inj G x y Hnd Hx Hy). lia. }
  apply rblocks_ext. intros d.
  destruct (gwrite_at G d) as [w|] eqn:Hd.
  - destruct (gwrite_at_inv G d w Hnd Hd) as [Hw Hwix].
    assert (Huniq : ∀ y, y ∈ gwrites G → grank G y = d → y = w).
    { intros y Hy HP. rewrite (grank_write y Hy) in HP.
      apply (gwix_inj G y w Hnd Hy Hw). lia. }
    assert (E1 : filter (λ x : geid, grank G x = d)
                        (filter (gis_w G) (gevs G)) = [w]).
    { apply filter_unique.
      - by apply list_relations.NoDup_filter, gevs_nodup.
      - by apply Hel.
      - rewrite (grank_write w Hw). exact Hwix.
      - intros y Hy HP. apply Huniq; [by apply Hel|exact HP]. }
    assert (E2 : filter (λ x : geid, grank G x = d) (gwrites G) = [w]).
    { apply filter_unique.
      - apply (gwrites_nodup G Hnd).
      - exact Hw.
      - rewrite (grank_write w Hw). exact Hwix.
      - exact Huniq. }
    by rewrite E1 E2.
  - assert (Hno : ∀ e, e ∈ gwrites G → grank G e ≠ d).
    { intros e He Heq. rewrite (grank_write e He) in Heq.
      rewrite -Heq (gwrite_at_gwix G e He) in Hd. done. }
    assert (E1 : filter (λ x : geid, grank G x = d)
                        (filter (gis_w G) (gevs G)) = []).
    { apply filter_no. intros e He. apply Hno. by apply Hel. }
    assert (E2 : filter (λ x : geid, grank G x = d) (gwrites G) = []).
    { apply filter_no. exact Hno. }
    by rewrite E1 E2.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** 3.7 The candidate's trace and log *)

Lemma lin_tr_lookup k e :
  glin_eids G !! k = Some e → cd_tr (lin_cand G) !! k = Some (glin_step G e).
Proof. intros H. by rewrite /lin_cand /= list_lookup_fmap H. Qed.

Lemma lin_tr_lookup_inv k s :
  cd_tr (lin_cand G) !! k = Some s →
  ∃ e, glin_eids G !! k = Some e ∧ s = glin_step G e.
Proof.
  rewrite /lin_cand /= list_lookup_fmap.
  destruct (glin_eids G !! k) as [e|] eqn:He; simpl; [|done].
  intros Heq; simplify_eq. by exists e.
Qed.

Lemma lin_tr_len : length (cd_tr (lin_cand G)) = length (glin_eids G).
Proof. by rewrite /lin_cand /= length_fmap. Qed.

Lemma lin_lbl k e : glin_eids G !! k = Some e → gx_lbl G e = Some (glbl G e).
Proof.
  intros H. destruct (glin_lookup_lbl k e H) as [l Hl]. by rewrite /glbl Hl.
Qed.

Lemma es_wmsg_glin e : es_wmsg (glin_step G e) = gmsg G e.
Proof.
  rewrite /es_wmsg /gmsg /glin_step /glbl /=.
  destruct (gx_lbl G e) as [l|]; [|done]. simpl.
  by destruct (lb_wr l) as [[b vs]|].
Qed.

Lemma tr_msgs_omap (l : list estep) : tr_msgs l = omap es_wmsg l.
Proof.
  induction l as [|s l IH]; [done|].
  csimpl. rewrite es_msg_wmsg. destruct (es_wmsg s); by rewrite IH.
Qed.

Lemma omap_glin (l : list geid) :
  omap es_wmsg (glin_step G <$> l) = omap (gmsg G) l.
Proof.
  induction l as [|e l IH]; [done|].
  rewrite fmap_cons. csimpl. rewrite es_wmsg_glin.
  destruct (gmsg G e); by rewrite IH.
Qed.

Lemma lin_log_take k :
  cd_log (lin_cand G) k = omap (gmsg G) (take k (glin_eids G)).
Proof. by rewrite /cd_log /lin_cand /= -fmap_take tr_msgs_omap omap_glin. Qed.

Lemma gmsg_is_w e : is_Some (gmsg G e) ↔ gis_w G e = true.
Proof.
  rewrite /gmsg /gis_w. destruct (gx_lbl G e) as [l|];
    [|split; [by intros [? ?]|done]].
  destruct (lb_wr l) as [[b vs]|] eqn:Hw.
  - split; [intros _; by eapply lb_wr_is_w|intros _; by eexists].
  - split; [by intros []|]. intros Hb.
    destruct (lb_is_w_wr l Hb) as (b & vs & Hc). by rewrite Hc in Hw.
Qed.

Lemma omap_gmsg_len (l : list geid) :
  length (omap (gmsg G) l) = length (filter (gis_w G) l).
Proof.
  induction l as [|e l IH]; [done|]. rewrite filter_cons. csimpl.
  destruct (gmsg G e) as [m|] eqn:Hm.
  - case_decide as Hb; [by rewrite /= IH|].
    exfalso. apply Hb, Is_true_true_2, gmsg_is_w. by eexists.
  - case_decide as Hb; [|exact IH].
    exfalso. apply Is_true_true_1 in Hb. apply gmsg_is_w in Hb as [? Hs].
    by rewrite Hm in Hs.
Qed.

Lemma lin_log_len k : length (cd_log (lin_cand G) k) = lin_nw G k.
Proof. by rewrite lin_log_take omap_gmsg_len. Qed.

Lemma filter_take_mono {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) k k' :
  (k ≤ k')%nat →
  (length (filter P (take k l)) ≤ length (filter P (take k' l)))%nat.
Proof.
  intros Hle.
  rewrite -(take_drop k (take k' l)) take_take Nat.min_l; [done|].
  rewrite list_basics.filter_app length_app. lia.
Qed.

Lemma lin_nw_mono k k' : (k ≤ k')%nat → (lin_nw G k ≤ lin_nw G k')%nat.
Proof. intros Hle. by apply filter_take_mono. Qed.

Lemma lin_nw_S k e :
  glin_eids G !! k = Some e → gis_w G e = true →
  lin_nw G (S k) = S (lin_nw G k).
Proof.
  intros He Hw. rewrite /lin_nw (take_S_r _ _ _ He) list_basics.filter_app.
  rewrite filter_cons. case_decide as Hb; [|exfalso; by apply Hb, Is_true_true_2].
  rewrite filter_nil length_app /=. lia.
Qed.

(** (P2) The write at trace index [k] is [gwrites G] entry number
    [lin_nw G k] — the trace's writes come out in gmo order. *)
Lemma lin_gwrites_split k e :
  glin_eids G !! k = Some e → gis_w G e = true →
  gwrites G !! lin_nw G k = Some e.
Proof.
  intros He Hw. rewrite -glin_writes.
  rewrite -(take_drop (S k) (glin_eids G)) list_basics.filter_app.
  rewrite (take_S_r _ _ _ He) list_basics.filter_app filter_cons.
  case_decide as Hb; [|exfalso; by apply Hb, Is_true_true_2].
  rewrite filter_nil -app_assoc lookup_app_r; [rewrite /lin_nw; lia|].
  by rewrite /lin_nw Nat.sub_diag.
Qed.

Lemma lin_ts_write k e :
  glin_eids G !! k = Some e → gis_w G e = true →
  ev_ts (cand_exec (lin_cand G)) (ev_at k) = gwix G e.
Proof.
  intros He Hw.
  assert (Hk : (k ≤ length (cd_tr (lin_cand G)))%nat).
  { rewrite lin_tr_len. apply lookup_lt_Some in He. lia. }
  rewrite (cand_ev_ts (lin_cand G) k Hk) lin_log_len.
  symmetry. apply (gwix_of_lookup G (lin_nw G k) e Hnd).
  by apply lin_gwrites_split.
Qed.

(** (P3) A read's source has already been emitted. *)
Lemma lin_source_before k r a i v :
  glin_eids G !! k = Some r → greads_byte G r a (S i) v →
  ∃ kw w, gwrite_at G (S i) = Some w ∧ glin_eids G !! kw = Some w ∧
          (kw < k)%nat.
Proof.
  intros Hk Hrd.
  destruct (proj1 (Hlv r a (S i) v Hrd)) as (w & Hwa & Hwb & _).
  pose proof (grf_gmo r a i v w Hrd Hwa) as Hmo.
  destruct (gwrite_at_inv G (S i) w Hnd Hwa) as [Hw Hwix].
  destruct (glin_index w (gwrites_lbl w Hw)) as [kw Hkw].
  exists kw, w. split_and!; [done|done|].
  apply (glin_rank_lt kw k w r Hkw Hk).
  rewrite (grank_write w Hw).
  assert (Hrl : is_Some (gx_lbl G r)) by by eapply greads_byte_lbl.
  pose proof Hrl as Hrl'. apply gx_lbl_bounds in Hrl' as [Hri Hrk].
  rewrite /grank. destruct r as [ir kr]; simpl in Hri, Hrk.
  destruct (gnxw G (ir, kr)) as [w'|] eqn:Hf; last first.
  { pose proof (gwix_le G w Hw). simpl. lia. }
  destruct (gnxw_Some G ir kr w' Hf) as (m & -> & Hkm & Hm & Hwm & _).
  assert (Hmo' : gmo_lt G w (ir, m)).
  { destruct (decide (kr = m)) as [->|Hne]; [exact Hmo|].
    apply (gmo_lt_trans G w (ir, kr) (ir, m) Hmo).
    apply H14; [| |by apply gis_w_glbl_is; [by apply glbl_some|]].
    - split_and!; simpl; [done|lia| |by apply glbl_some].
      by apply gx_lbl_bounds.
    - apply (gwf_gmo_mem G (ir, kr) Hwf). by eapply greads_byte_mem. }
  apply (gwix_gpos_lt G w (ir, m) Hnd Hw
           (gis_w_gwrites G (ir, m) Hwf (glbl_some G ir m Hri Hm) Hwm)).
  by apply Hmo'.
Qed.

Lemma lin_read_ts_le k r a t v :
  glin_eids G !! k = Some r → greads_byte G r a t v →
  (t ≤ length (cd_log (lin_cand G) k))%nat.
Proof.
  intros Hk Hrd. rewrite lin_log_len. destruct t as [|i]; [lia|].
  destruct (lin_source_before k r a i v Hk Hrd) as (kw & w & Hwa & Hkw & Hlt).
  destruct (gwrite_at_inv G (S i) w Hnd Hwa) as [Hw Hwix].
  pose proof (lin_gwrites_split kw w Hkw (gwrites_isw w Hw)) as Hsp.
  rewrite (gwix_of_lookup G (lin_nw G kw) w Hnd Hsp) in Hwix.
  pose proof (lin_nw_S kw w Hkw (gwrites_isw w Hw)) as HS.
  pose proof (lin_nw_mono (S kw) k ltac:(lia)). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.8 The final log IS [gwrites G] through [gmsg] *)

Lemma omap_gmsg_filter (l : list geid) :
  omap (gmsg G) l = omap (gmsg G) (filter (gis_w G) l).
Proof.
  induction l as [|e l IH]; [done|]. rewrite filter_cons.
  case_decide as Hb.
  - csimpl. destruct (gmsg G e); by rewrite IH.
  - csimpl. destruct (gmsg G e) as [m|] eqn:Hm; [|exact IH].
    exfalso. apply Hb, Is_true_true_2, gmsg_is_w. by eexists.
Qed.

Lemma lin_full_log :
  cd_log (lin_cand G) (length (cd_tr (lin_cand G))) = omap (gmsg G) (gwrites G).
Proof.
  assert (Hge : take (length (glin_eids G)) (glin_eids G) = glin_eids G)
    by (apply take_ge; lia).
  by rewrite lin_log_take lin_tr_len Hge omap_gmsg_filter glin_writes.
Qed.

Lemma lin_ex_log :
  ex_log (cand_exec (lin_cand G)) = omap (gmsg G) (gwrites G).
Proof. by rewrite cand_ex_log lin_full_log. Qed.

Lemma lin_ex_img : ex_img (cand_exec (lin_cand G)) = gx_img G.
Proof. by rewrite cand_ex_img. Qed.

Lemma omap_lookup_all {A B} (f : A → option B) (l : list A) i x :
  (∀ y, y ∈ l → is_Some (f y)) → l !! i = Some x → omap f l !! i = f x.
Proof.
  revert i. induction l as [|a l IH]; intros i Hall Hi.
  { by rewrite lookup_nil in Hi. }
  destruct (Hall a ltac:(by left)) as [b Hb]. csimpl. rewrite Hb.
  destruct i as [|i]; simpl in Hi.
  - simplify_eq. by rewrite /= Hb.
  - simpl. apply IH; [intros y Hy; apply Hall; by right|done].
Qed.

Lemma lin_log_full_lookup i w :
  gwrites G !! i = Some w → omap (gmsg G) (gwrites G) !! i = gmsg G w.
Proof.
  intros Hi. apply omap_lookup_all; [|done].
  intros y Hy. apply gmsg_is_w. by apply gwrites_isw.
Qed.

Lemma gmsg_byte w a v :
  gwrites_byte G w a v → ∃ m, gmsg G w = Some m ∧ msg_byte m a = Some v.
Proof.
  intros (l & base & vs & j & Hl & Hwr & Hv & Ha).
  exists (WMsg base vs (Some w.1) (lb_cls l)). split.
  - by rewrite /gmsg Hl Hwr.
  - rewrite /msg_byte /= -Ha bool_decide_eq_true_2; [rewrite /acc_addr; lia|].
    by replace (Z.to_nat (acc_addr base j - base)) with j
      by (rewrite /acc_addr; lia).
Qed.

Lemma gmsg_byte_inv w m a v :
  gmsg G w = Some m → msg_byte m a = Some v → gwrites_byte G w a v.
Proof.
  rewrite /gmsg. destruct (gx_lbl G w) as [l|] eqn:Hl; [|done].
  destruct (lb_wr l) as [[base vs]|] eqn:Hwr; [|done].
  intros Heq; simplify_eq. rewrite /msg_byte /=.
  destruct (bool_decide (base ≤ a)%Z) eqn:Hb; [|done].
  apply bool_decide_eq_true in Hb. intros Hv.
  exists l, base, vs, (Z.to_nat (a - base)). split_and!; [done|done|done|].
  rewrite /acc_addr. lia.
Qed.

Lemma lin_log_byte_final t w a v :
  gwrite_at G t = Some w → gwrites_byte G w a v →
  log_byte (gx_img G) (omap (gmsg G) (gwrites G)) t a = Some v.
Proof.
  destruct t as [|i]; [done|]. intros Hw Hb.
  rewrite log_byte_S (lin_log_full_lookup i w Hw).
  destruct (gmsg_byte w a v Hb) as (m & Hm & Hmb). by rewrite Hm /=.
Qed.

Lemma lin_log_byte_final_inv t w a v :
  gwrite_at G t = Some w →
  log_byte (gx_img G) (omap (gmsg G) (gwrites G)) t a = Some v →
  gwrites_byte G w a v.
Proof.
  destruct t as [|i]; [done|]. intros Hw Hlb.
  rewrite log_byte_S (lin_log_full_lookup i w Hw) in Hlb.
  destruct (gmsg G w) as [m|] eqn:Hm; [|done]. simpl in Hlb.
  by eapply gmsg_byte_inv.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 3.9 The dictionary: candidate relations ARE graph relations *)

Lemma lin_is_W k e :
  glin_eids G !! k = Some e →
  (is_W (cand_exec (lin_cand G)) (ev_at k) ↔ gis_w G e = true).
Proof.
  intros Hk. rewrite /is_W /gis_w (lin_lbl k e Hk). split.
  - intros (s & Hs & Hw).
    rewrite cand_ex_tr (lin_tr_lookup k e Hk) in Hs. by simplify_eq.
  - intros Hw. exists (glin_step G e). split; [|exact Hw].
    rewrite cand_ex_tr. by apply lin_tr_lookup.
Qed.

Lemma lin_wr_b k e a :
  glin_eids G !! k = Some e →
  (wr_b (cand_exec (lin_cand G)) a (ev_at k) ↔ ∃ v, gwrites_byte G e a v).
Proof.
  intros Hk. split.
  - intros [HW Hwr]. pose proof (proj1 (lin_is_W k e Hk) HW) as Hw.
    rewrite /ev_writes lin_ex_img lin_ex_log (lin_ts_write k e Hk Hw) in Hwr.
    destruct Hwr as [v Hv]. exists v.
    apply (lin_log_byte_final_inv (gwix G e) e a v); [|exact Hv].
    apply gwrite_at_gwix, (gis_w_gwrites G e Hwf);
      [by eapply glin_lookup_lbl|done].
  - intros [v Hv].
    assert (Hw : gis_w G e = true) by by eapply gwrites_byte_isw.
    split; [by apply (lin_is_W k e Hk)|].
    rewrite /ev_writes lin_ex_img lin_ex_log (lin_ts_write k e Hk Hw).
    exists v. apply (lin_log_byte_final (gwix G e) e a v); [|exact Hv].
    apply gwrite_at_gwix, (gis_w_gwrites G e Hwf);
      [by eapply glin_lookup_lbl|done].
Qed.

Lemma lin_reads_at k e a t v :
  glin_eids G !! k = Some e →
  (reads_at (cand_exec (lin_cand G)) k a t v ↔ greads_byte G e a t v).
Proof.
  intros Hk. rewrite /reads_at /greads_byte cand_ex_tr. split.
  - intros (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha).
    rewrite (lin_tr_lookup k e Hk) in Hs. simplify_eq.
    exists (glbl G e), base, ts, vs, j.
    split_and!; [exact (lin_lbl k e Hk)|done|done|done|by symmetry].
  - intros (l & base & ts & vs & j & Hl & Hrd & Hj & Hv & Ha).
    rewrite (lin_lbl k e Hk) in Hl. simplify_eq.
    exists (glin_step G e), base, ts, vs, j.
    split_and!; [exact (lin_tr_lookup k e Hk)|done|done|done|by symmetry].
Qed.

Lemma lin_rd_b k e a :
  glin_eids G !! k = Some e →
  (rd_b (cand_exec (lin_cand G)) a (ev_at k) ↔ ∃ t v, greads_byte G e a t v).
Proof.
  intros Hk. rewrite /rd_b. split.
  - intros (k' & t & v & Heq & Hr). simplify_eq.
    exists t, v. by apply (lin_reads_at k' e a t v Hk).
  - intros (t & v & Hr). exists k, t, v. split; [done|].
    by apply (lin_reads_at k e a t v Hk).
Qed.

Lemma lin_acc_b k e a :
  glin_eids G !! k = Some e →
  (acc_b (cand_exec (lin_cand G)) a (ev_at k) ↔ gaccesses G e a).
Proof.
  intros Hk. rewrite /acc_b /gaccesses (lin_wr_b k e a Hk) (lin_rd_b k e a Hk).
  done.
Qed.

Lemma lin_po_dict k1 k2 e1 e2 :
  glin_eids G !! k1 = Some e1 → glin_eids G !! k2 = Some e2 →
  (po (cand_exec (lin_cand G)) (ev_at k1) (ev_at k2) ↔ gpo G e1 e2).
Proof.
  intros H1 H2. rewrite /po /gpo cand_ex_tr. split.
  - intros (a & b & s1 & s2 & Ha & Hb & Hlt & Hs1 & Hs2 & Hag). simplify_eq.
    rewrite (lin_tr_lookup a e1 H1) in Hs1.
    rewrite (lin_tr_lookup b e2 H2) in Hs2. simplify_eq. simpl in Hag.
    split_and!; [done| |by eapply glin_lookup_lbl|by eapply glin_lookup_lbl].
    by apply (glin_po_iff a b e1 e2 H1 H2 Hag).
  - intros (Hag & Hlt & _ & _).
    exists k1, k2, (glin_step G e1), (glin_step G e2).
    split_and!; [done|done| |by apply lin_tr_lookup|by apply lin_tr_lookup|done].
    by eapply glin_po_lt.
Qed.

Lemma greads_byte_is_r e a t v : greads_byte G e a t v → glbl_is G e lb_is_r.
Proof.
  intros (l & base & ts & vs & j & Hl & Hrd & _). exists l. split; [done|].
  by eapply lb_rd_is_r.
Qed.

Lemma gwrites_byte_is_w e a v : gwrites_byte G e a v → glbl_is G e lb_is_w.
Proof.
  intros (l & base & vs & j & Hl & Hwr & _). exists l. split; [done|].
  by eapply lb_wr_is_w.
Qed.

Lemma lin_src_gmo e a t v :
  greads_byte G e a t v → (0 < t)%nat →
  ∃ w, gwrite_at G t = Some w ∧ gwrites_byte G w a v ∧ gmo_lt G w e ∧
       gwix G w = t.
Proof.
  intros Hg Ht. destruct t as [|i]; [lia|].
  destruct (proj1 (Hlv e a (S i) v Hg)) as (w & Hwa & Hwb & _).
  exists w. split_and!; [done|done|by eapply grf_gmo|].
  by destruct (gwrite_at_inv G (S i) w Hnd Hwa) as [_ ?].
Qed.

(* ====================================================================== *)
(** * 4. THE SIX OBLIGATIONS *)

Lemma gx_lbl_row_lookup e l :
  gx_lbl G e = Some l →
  gx_prog G !! e.1 = Some (grow G e.1) ∧ grow G e.1 !! e.2 = Some l.
Proof.
  intros Hl. assert (Hb : is_Some (gx_lbl G e)) by by eexists.
  apply gx_lbl_bounds in Hb as [Hi Hk].
  rewrite /gx_lbl (grow_lookup G e.1 Hi) /= in Hl.
  split; [by apply grow_lookup|exact Hl].
Qed.

(** ** 4.1 [cand_shape] — [gwf]'s shape clause, verbatim *)

Lemma lin_shape : cand_shape (lin_cand G).
Proof.
  intros k s Hs. destruct (lin_tr_lookup_inv k s Hs) as (e & Hk & ->).
  destruct (glin_lookup_lbl k e Hk) as [l Hl].
  assert (Hgl : glbl G e = l) by (rewrite /glbl Hl //).
  simpl. rewrite Hgl.
  destruct (gx_lbl_row_lookup e l Hl) as [Hp Hr].
  destruct Hwf as (_ & _ & Hsh). by apply (Hsh e.1 (grow G e.1) e.2 l).
Qed.

(** ** 4.2 [cand_values] — (P2)+(P3) put the source at log position [t] *)

Lemma lin_values : cand_values (lin_cand G).
Proof.
  intros k s base ts vs Hs Hrd j t v Hj Hv.
  destruct (lin_tr_lookup_inv k s Hs) as (e & Hk & ->).
  simpl in Hrd.
  assert (Hg : greads_byte G e (acc_addr base j) t v).
  { exists (glbl G e), base, ts, vs, j.
    split_and!; [exact (lin_lbl k e Hk)|exact Hrd|done|done|done]. }
  change (cd_img (lin_cand G)) with (gx_img G).
  destruct t as [|i].
  - rewrite log_byte_0. by apply (proj1 (Hlv e (acc_addr base j) 0%nat v Hg)).
  - destruct (proj1 (Hlv e (acc_addr base j) (S i) v Hg)) as (w & Hwa & Hwb & _).
    assert (Hle : (S i ≤ length (cd_log (lin_cand G) k))%nat)
      by by eapply lin_read_ts_le.
    assert (Hkl : (k ≤ length (cd_tr (lin_cand G)))%nat).
    { apply lookup_lt_Some in Hs. lia. }
    destruct (cd_log_split (lin_cand G) k (length (cd_tr (lin_cand G))) Hkl)
      as [rest Hrest].
    rewrite -(log_byte_app (gx_img G) (cd_log (lin_cand G) k) rest (S i)
                (acc_addr base j) Hle) -Hrest lin_full_log.
    by apply (lin_log_byte_final (S i) w (acc_addr base j) v).
Qed.

(** ** 4.3 [ax_atomicity] — [gatomicity] through (P2) *)

Lemma lin_atomicity : ax_atomicity (cand_exec (lin_cand G)).
Proof.
  intros kr a w0 w HW Hrf Hw Hgt Hlt.
  destruct w as [|kw]; [simpl in Hgt; lia|].
  pose proof HW as (sr & Hsr & _).
  destruct (lin_tr_lookup_inv kr sr Hsr) as (er & Hkr & _).
  pose proof (proj1 Hw) as (sw & Hsw & _).
  destruct (lin_tr_lookup_inv kw sw Hsw) as (ew & Hkw & _).
  destruct (proj1 (lin_wr_b kw ew a Hkw) Hw) as [v' Hwb].
  assert (Hwe : gis_w G ew = true) by by eapply gwrites_byte_isw.
  destruct Hrf as (_ & k & t0 & v0 & Heq & Hr & Hts0).
  assert (k = kr) as -> by (by simplify_eq).
  assert (Hgr : greads_byte G er a t0 v0)
    by by apply (lin_reads_at kr er a t0 v0 Hkr).
  apply (Hat er a t0 v0 Hgr
           (gis_w_glbl_is er (glin_lookup_lbl kr er Hkr)
              (proj1 (lin_is_W kr er Hkr) HW)) ew v' Hwb).
  rewrite (lin_ts_write kw ew Hkw Hwe) in Hgt, Hlt.
  rewrite (lin_ts_write kr er Hkr (proj1 (lin_is_W kr er Hkr) HW)) in Hlt.
  rewrite Hts0 in Hgt. split; [exact Hgt|exact Hlt].
Qed.

(** ** 4.4 [ax_coherence] — ppo 1–3 plus the load-value axiom's co-maximality *)

Lemma lin_ets_wr k e a :
  glin_eids G !! k = Some e → wr_b (cand_exec (lin_cand G)) a (ev_at k) →
  ets (cand_exec (lin_cand G)) a (ev_at k) = gwix G e.
Proof.
  intros Hk Hw. rewrite (ets_wr _ a _ Hw).
  apply (lin_ts_write k e Hk), (lin_is_W k e Hk), Hw.
Qed.

Lemma lin_ets_rd k e a t v :
  glin_eids G !! k = Some e → ¬ wr_b (cand_exec (lin_cand G)) a (ev_at k) →
  greads_byte G e a t v → ets (cand_exec (lin_cand G)) a (ev_at k) = t.
Proof.
  intros Hk Hn Hg. apply (ets_rd _ a k t v Hn).
  by apply (lin_reads_at k e a t v Hk).
Qed.

Lemma lin_nwr_read k e a :
  glin_eids G !! k = Some e → ¬ wr_b (cand_exec (lin_cand G)) a (ev_at k) →
  gaccesses G e a → ∃ t v, greads_byte G e a t v.
Proof.
  intros Hk Hn [Hw|Hr]; [|exact Hr].
  exfalso. apply Hn. by apply (lin_wr_b k e a Hk).
Qed.

(** THE COHERENCE STEP: same-byte program order does not lower the byte's
    timestamp.  Every arm is [gvisible] arithmetic. *)
Lemma lin_poloc_ets k1 k2 e1 e2 a :
  glin_eids G !! k1 = Some e1 → glin_eids G !! k2 = Some e2 →
  gpo G e1 e2 → gmo_lt G e1 e2 → gaccesses G e1 a → gaccesses G e2 a →
  (ets (cand_exec (lin_cand G)) a (ev_at k1) ≤
   ets (cand_exec (lin_cand G)) a (ev_at k2))%nat.
Proof.
  intros H1 H2 Hpo Hmo Ha1 Ha2.
  destruct (wr_b_dec (cand_exec (lin_cand G)) a (ev_at k2)) as [Hw2|Hn2].
  - rewrite (lin_ets_wr k2 e2 a H2 Hw2).
    destruct (proj1 (lin_wr_b k2 e2 a H2) Hw2) as [v2 Hwb2].
    assert (He2 : e2 ∈ gwrites G) by by eapply gwrites_byte_gw.
    destruct (wr_b_dec (cand_exec (lin_cand G)) a (ev_at k1)) as [Hw1|Hn1].
    + rewrite (lin_ets_wr k1 e1 a H1 Hw1).
      destruct (proj1 (lin_wr_b k1 e1 a H1) Hw1) as [v1 Hwb1].
      apply Nat.lt_le_incl.
      apply (gwix_gpos_lt G e1 e2 Hnd (gwrites_byte_gw e1 a v1 Hwb1) He2).
      by apply Hmo.
    + destruct (lin_nwr_read k1 e1 a H1 Hn1 Ha1) as (t1 & v1 & Hg1).
      rewrite (lin_ets_rd k1 e1 a t1 v1 H1 Hn1 Hg1).
      destruct t1 as [|i1]; [lia|].
      destruct (lin_src_gmo e1 a (S i1) v1 Hg1 ltac:(lia))
        as (w0 & Hwa & Hwb & Hmo0 & Hwix).
      rewrite -Hwix. apply Nat.lt_le_incl.
      apply (gwix_gpos_lt G w0 e2 Hnd (gwrites_byte_gw w0 a v1 Hwb) He2).
      by apply (gmo_lt_trans G w0 e1 e2 Hmo0 Hmo).
  - destruct (lin_nwr_read k2 e2 a H2 Hn2 Ha2) as (t2 & v2 & Hg2).
    rewrite (lin_ets_rd k2 e2 a t2 v2 H2 Hn2 Hg2).
    destruct (wr_b_dec (cand_exec (lin_cand G)) a (ev_at k1)) as [Hw1|Hn1].
    + rewrite (lin_ets_wr k1 e1 a H1 Hw1).
      destruct (proj1 (lin_wr_b k1 e1 a H1) Hw1) as [v1 Hwb1].
      by apply (gcomax e2 a t2 v2 e1 v1 Hg2 Hwb1 (or_introl Hmo)).
    + destruct (lin_nwr_read k1 e1 a H1 Hn1 Ha1) as (t1 & v1 & Hg1).
      rewrite (lin_ets_rd k1 e1 a t1 v1 H1 Hn1 Hg1).
      destruct t1 as [|i1]; [lia|].
      destruct (lin_src_gmo e1 a (S i1) v1 Hg1 ltac:(lia))
        as (w0 & Hwa & Hwb & Hmo0 & Hwix).
      rewrite -Hwix.
      apply (gcomax e2 a t2 v2 w0 v1 Hg2 Hwb
               (or_introl (gmo_lt_trans G w0 e1 e2 Hmo0 Hmo))).
Qed.

Lemma lin_read_ts_le' k a t v :
  reads_at (cand_exec (lin_cand G)) k a t v →
  (t ≤ length (cd_log (lin_cand G) k))%nat.
Proof.
  intros Hr. pose proof Hr as (s & base & ts & vs & j & Hs & _).
  destruct (lin_tr_lookup_inv k s Hs) as (e & Hk & _).
  apply (lin_read_ts_le k e a t v Hk). by apply (lin_reads_at k e a t v Hk).
Qed.

Lemma lin_coh_lexlt a e1 e2 :
  coh_rel (cand_exec (lin_cand G)) a e1 e2 →
  lexlt (ets (cand_exec (lin_cand G)) a e1, ev_ix e1)
        (ets (cand_exec (lin_cand G)) a e2, ev_ix e2).
Proof.
  intros [Hpl|[Hrf|[Hco|Hfr]]].
  - destruct Hpl as ((k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag)
                     & Ha1 & Ha2).
    destruct (lin_tr_lookup_inv k1 s1 Hs1) as (g1 & Hk1 & ->).
    destruct (lin_tr_lookup_inv k2 s2 Hs2) as (g2 & Hk2 & ->).
    simpl in Hag.
    assert (Hpo : gpo G g1 g2).
    { split_and!; [done| |by eapply glin_lookup_lbl|by eapply glin_lookup_lbl].
      by apply (glin_po_iff k1 k2 g1 g2 Hk1 Hk2 Hag). }
    assert (Hg1 : gaccesses G g1 a) by by apply (lin_acc_b k1 g1 a Hk1).
    assert (Hg2 : gaccesses G g2 a) by by apply (lin_acc_b k2 g2 a Hk2).
    assert (Hmo : gmo_lt G g1 g2).
    { apply Hppo. left. split; [exact Hpo|]. by exists a. }
    pose proof (lin_poloc_ets k1 k2 g1 g2 a Hk1 Hk2 Hpo Hmo Hg1 Hg2) as Hle.
    rewrite /lexlt /=.
    destruct (decide (ets (cand_exec (lin_cand G)) a (ev_at k1)
                      = ets (cand_exec (lin_cand G)) a (ev_at k2)))
      as [Heq|Hne]; [right; split; [exact Heq|lia]|left; lia].
  - pose proof Hrf as Hrf'.
    destruct Hrf' as (Hw & k & t & v & Heq & Hr & Hts). subst e2.
    pose proof (cand_rf_ix (lin_cand G) a e1 k lin_values Hrf) as Hix.
    rewrite (ets_wr _ a e1 Hw) Hts.
    destruct (wr_b_dec (cand_exec (lin_cand G)) a (ev_at k)) as [Hw2|Hn2].
    + rewrite (ets_wr _ a _ Hw2) ev_ts_at.
      pose proof (lin_read_ts_le' k a t v Hr) as Htl.
      pose proof Hr as (s & base & ts & vs & j & Hs & _).
      assert (Hkl : (k ≤ length (cd_tr (lin_cand G)))%nat).
      { rewrite cand_ex_tr in Hs. apply lookup_lt_Some in Hs. lia. }
      rewrite (cand_elog (lin_cand G) k Hkl). left. simpl. lia.
    + rewrite (ets_rd _ a k t v Hn2 Hr). right. split; [done|exact Hix].
  - destruct Hco as (Hw1 & Hw2 & Hlt).
    rewrite (ets_wr _ a e1 Hw1) (ets_wr _ a e2 Hw2). by left.
  - destruct Hfr as ((w0 & Hrf0 & Hco) & Hne).
    pose proof Hco as (Hw0 & Hw2 & Hlt).
    rewrite (ets_wr _ a e2 Hw2).
    pose proof Hrf0 as (_ & kr & t0 & v0 & Heq & Hr & Hts0). subst e1.
    destruct (wr_b_dec (cand_exec (lin_cand G)) a (ev_at kr)) as [Hw1|Hn1];
      last first.
    { rewrite (ets_rd _ a kr t0 v0 Hn1 Hr). left. simpl. lia. }
    destruct e2 as [|kw]; [simpl in Hlt; lia|].
    pose proof Hr as (sr & base & ts & vs & j & Hsr & _).
    destruct (lin_tr_lookup_inv kr sr Hsr) as (er & Hkr & _).
    pose proof (proj1 Hw2) as (sw & Hsw & _).
    destruct (lin_tr_lookup_inv kw sw Hsw) as (ew & Hkw & _).
    destruct (proj1 (lin_wr_b kw ew a Hkw) Hw2) as [v' Hwb].
    assert (Hwe : gis_w G ew = true) by by eapply gwrites_byte_isw.
    assert (Hwr : gis_w G er = true)
      by by apply (lin_is_W kr er Hkr), (proj1 Hw1).
    assert (Hgr : greads_byte G er a t0 v0)
      by by apply (lin_reads_at kr er a t0 v0 Hkr).
    rewrite (ets_wr _ a _ Hw1) (lin_ts_write kr er Hkr Hwr)
            (lin_ts_write kw ew Hkw Hwe).
    left. simpl.
    assert (Hlt0 : (t0 < gwix G ew)%nat).
    { rewrite -(lin_ts_write kw ew Hkw Hwe) -Hts0. exact Hlt. }
    assert (Hle : (gwix G ew < gwix G er)%nat → False).
    { intros Hc. apply (Hat er a t0 v0 Hgr
                          (gis_w_glbl_is er (glin_lookup_lbl kr er Hkr) Hwr)
                          ew v' Hwb). by split. }
    assert (Hnee : er ≠ ew).
    { intros Hc.
      assert (Hkk : kr = kw).
      { apply (NoDup_lookup (glin_eids G) kr kw er glin_nodup Hkr).
        by rewrite Hc. }
      apply Hne. by rewrite Hkk. }
    assert (Hwix : gwix G er ≠ gwix G ew).
    { intros Hc. apply Hnee.
      apply (gwix_inj G er ew Hnd
               (gis_w_gwrites G er Hwf (glin_lookup_lbl kr er Hkr) Hwr)
               (gwrites_byte_gw ew a v' Hwb) Hc). }
    lia.
Qed.

Lemma lin_coherence : ax_coherence (cand_exec (lin_cand G)).
Proof.
  intros a.
  apply (tc_lexlt _ (λ e, (ets (cand_exec (lin_cand G)) a e, ev_ix e))).
  intros x y Hxy. by apply lin_coh_lexlt.
Qed.

(** ** 4.5 [ax_ord] / [ax_rel_ord] — the ordering edges map to [gppo] *)

Lemma lin_fence_between k1 k2 e1 e2 pr pw sr sw :
  glin_eids G !! k1 = Some e1 → glin_eids G !! k2 = Some e2 →
  fence_between (cand_exec (lin_cand G)) k1 k2 pr pw sr sw →
  gfence_between G e1 e2 pr pw sr sw.
Proof.
  intros H1 H2 (kf & sf & s1 & s2 & Hlt1 & Hlt2 & Hs1 & Hsf & Hs2 & Hag1 & Hag2
                & Hlf).
  destruct (lin_tr_lookup_inv k1 s1 Hs1) as (q1 & Hq1 & ->).
  destruct (lin_tr_lookup_inv kf sf Hsf) as (qf & Hqf & ->).
  destruct (lin_tr_lookup_inv k2 s2 Hs2) as (q2 & Hq2 & ->).
  assert (q1 = e1) as -> by (rewrite H1 in Hq1; by simplify_eq).
  assert (q2 = e2) as -> by (rewrite H2 in Hq2; by simplify_eq).
  simpl in Hag1, Hag2, Hlf.
  assert (Hag : e1.1 = e2.1) by (rewrite Hag1 Hag2 //).
  split_and!; [exact Hag| |].
  - apply (proj1 (glin_po_iff k1 k2 e1 e2 H1 H2 Hag)). lia.
  - exists qf.2. split_and!.
    + apply (proj1 (glin_po_iff k1 kf e1 qf H1 Hqf Hag1)). lia.
    + apply (proj1 (glin_po_iff kf k2 qf e2 Hqf H2 Hag2)). lia.
    + assert (Heq : (e1.1, qf.2) = qf) by (rewrite Hag1; by destruct qf).
      by rewrite Heq (lin_lbl kf qf Hqf) Hlf.
Qed.

Lemma lin_acq_po_gmo k1 k2 g1 g2 :
  glin_eids G !! k1 = Some g1 → glin_eids G !! k2 = Some g2 →
  acq_po (cand_exec (lin_cand G)) (ev_at k1) (ev_at k2) → gmo_lt G g1 g2.
Proof.
  intros H1 H2 (n1 & n2 & s1 & s2 & Ha & Hb & Hlt & Hs1 & Hs2 & Hag & Hisr
                & Haq).
  simplify_eq.
  destruct (lin_tr_lookup_inv n1 s1 Hs1) as (q1 & Hq1 & ->).
  destruct (lin_tr_lookup_inv n2 s2 Hs2) as (q2 & Hq2 & ->).
  assert (q1 = g1) as -> by (rewrite H1 in Hq1; by simplify_eq).
  assert (q2 = g2) as -> by (rewrite H2 in Hq2; by simplify_eq).
  simpl in Hag, Hisr, Haq.
  apply Hppo. right. right. left. split_and!.
  - split_and!;
      [exact Hag| |by eapply glin_lookup_lbl|by eapply glin_lookup_lbl].
    by apply (glin_po_iff n1 n2 g1 g2 H1 H2 Hag).
  - exists (glbl G g1). split; [exact (lin_lbl n1 g1 H1)|exact Hisr].
  - exists (glbl G g1). split; [exact (lin_lbl n1 g1 H1)|exact Haq].
Qed.

Lemma lin_rel_acq_gmo k1 k2 g1 g2 :
  glin_eids G !! k1 = Some g1 → glin_eids G !! k2 = Some g2 →
  rel_acq_po (cand_exec (lin_cand G)) (ev_at k1) (ev_at k2) → gmo_lt G g1 g2.
Proof.
  intros H1 H2 (n1 & n2 & s1 & s2 & Ha & Hb & Hlt & Hs1 & Hs2 & Hag & Hw1 & Hrl1
                & Hr2 & Haq2).
  simplify_eq.
  destruct (lin_tr_lookup_inv n1 s1 Hs1) as (q1 & Hq1 & ->).
  destruct (lin_tr_lookup_inv n2 s2 Hs2) as (q2 & Hq2 & ->).
  assert (q1 = g1) as -> by (rewrite H1 in Hq1; by simplify_eq).
  assert (q2 = g2) as -> by (rewrite H2 in Hq2; by simplify_eq).
  simpl in Hag, Hw1, Hrl1, Hr2, Haq2.
  apply Hppo. right. right. right. split_and!.
  - split_and!;
      [exact Hag| |by eapply glin_lookup_lbl|by eapply glin_lookup_lbl].
    by apply (glin_po_iff n1 n2 g1 g2 H1 H2 Hag).
  - exists (glbl G g1). split; [exact (lin_lbl n1 g1 H1)|exact Hw1].
  - exists (glbl G g1). split; [exact (lin_lbl n1 g1 H1)|exact Hrl1].
  - exists (glbl G g2). split; [exact (lin_lbl n2 g2 H2)|exact Hr2].
  - exists (glbl G g2). split; [exact (lin_lbl n2 g2 H2)|exact Haq2].
Qed.

Lemma lin_fr_bound k2 e2 a w :
  glin_eids G !! k2 = Some e2 →
  fr_b (cand_exec (lin_cand G)) a (ev_at k2) w →
  ∃ kw ew, w = ev_at kw ∧ glin_eids G !! kw = Some ew ∧ ew ∈ gwrites G ∧
           ev_ts (cand_exec (lin_cand G)) w = gwix G ew ∧
           (gpos G e2 ≤ gpos G ew)%nat.
Proof.
  intros Hk2 ((w0 & Hrf & Hco) & Hne).
  pose proof Hco as (Hw0 & Hw & Hlt).
  pose proof Hrf as (_ & k & t0 & v0 & Heq & Hr & Hts0).
  assert (k = k2) as -> by (by simplify_eq).
  destruct w as [|kw]; [simpl in Hlt; lia|].
  pose proof (proj1 Hw) as (sw & Hsw & _).
  destruct (lin_tr_lookup_inv kw sw Hsw) as (ew & Hkw & _).
  destruct (proj1 (lin_wr_b kw ew a Hkw) Hw) as [v' Hwb].
  assert (Hwe : gis_w G ew = true) by by eapply gwrites_byte_isw.
  assert (Hgr : greads_byte G e2 a t0 v0)
    by by apply (lin_reads_at k2 e2 a t0 v0 Hk2).
  exists kw, ew. split_and!; [done|done|by eapply gwrites_byte_gw| |].
  - exact (lin_ts_write kw ew Hkw Hwe).
  - apply (gfr_ge e2 a t0 v0 ew v' Hgr Hwb).
    rewrite -(lin_ts_write kw ew Hkw Hwe) -Hts0. exact Hlt.
Qed.

Lemma lin_pub_bound k1 e1 t :
  glin_eids G !! k1 = Some e1 →
  (pub_w (cand_exec (lin_cand G)) (ev_at k1) t ∨
   pub_r (cand_exec (lin_cand G)) (ev_at k1) t) →
  t = 0%nat ∨ ∃ u, u ∈ gwrites G ∧ gwix G u = t ∧ (gpos G u ≤ gpos G e1)%nat.
Proof.
  intros Hk [Hpw|Hpr].
  - right. pose proof Hpw as (HW & _ & Hts).
    assert (Hw : gis_w G e1 = true) by by apply (lin_is_W k1 e1 Hk).
    exists e1. split_and!; [|rewrite Hts; symmetry; exact (lin_ts_write k1 e1 Hk Hw)|lia].
    apply (gis_w_gwrites G e1 Hwf); [by eapply glin_lookup_lbl|done].
  - pose proof Hpr as (k & s & a & v & Heq & Hs & Hr & _).
    assert (k = k1) as -> by (by simplify_eq).
    destruct t as [|i]; [by left|]. right.
    assert (Hg : greads_byte G e1 a (S i) v)
      by by apply (lin_reads_at k1 e1 a (S i) v Hk).
    destruct (lin_src_gmo e1 a (S i) v Hg ltac:(lia))
      as (u & Hwa & Hwb & Hmo & Hwix).
    exists u. split_and!; [by eapply gwrites_byte_gw|exact Hwix|].
    destruct Hmo as (_ & _ & Hp). lia.
Qed.

Lemma lin_ord_core k1 k2 e1 e2 a w t :
  glin_eids G !! k1 = Some e1 → glin_eids G !! k2 = Some e2 →
  gmo_lt G e1 e2 →
  (pub_w (cand_exec (lin_cand G)) (ev_at k1) t ∨
   pub_r (cand_exec (lin_cand G)) (ev_at k1) t) →
  fr_b (cand_exec (lin_cand G)) a (ev_at k2) w →
  (t < ev_ts (cand_exec (lin_cand G)) w)%nat.
Proof.
  intros H1 H2 Hmo Hpub Hfr.
  destruct (lin_fr_bound k2 e2 a w H2 Hfr)
    as (kw & ew & -> & Hkw & Hew & Hts & Hge).
  rewrite Hts.
  destruct (lin_pub_bound k1 e1 t H1 Hpub) as [->|(u & Hu & Hux & Hup)].
  - by apply gwix_pos.
  - rewrite -Hux. apply (gwix_gpos_lt G u ew Hnd Hu Hew).
    destruct Hmo as (_ & _ & Hlt). lia.
Qed.

Lemma lin_read_at_2 k2 s2 a w :
  ex_tr (cand_exec (lin_cand G)) !! k2 = Some s2 →
  fr_b (cand_exec (lin_cand G)) a (ev_at k2) w →
  ∃ e2, glin_eids G !! k2 = Some e2 ∧ glbl_is G e2 lb_is_r.
Proof.
  intros Hs2 Hfr.
  destruct (lin_tr_lookup_inv k2 s2 Hs2) as (e2 & Hk2 & _).
  exists e2. split; [done|].
  destruct Hfr as ((w0 & (_ & k & t0 & v0 & Heq & Hr & _) & _) & _).
  assert (k = k2) as -> by (by simplify_eq).
  apply (greads_byte_is_r e2 a t0 v0).
  by apply (lin_reads_at k2 e2 a t0 v0 Hk2).
Qed.

Lemma lin_ord : ax_ord (cand_exec (lin_cand G)).
Proof.
  intros e1 k2 s2 a w t Hs2 Hcase Hfr.
  destruct (lin_read_at_2 k2 s2 a w Hs2 Hfr) as (e2 & Hk2 & Hr2).
  destruct Hcase as [[Hord Hpub]|[Hord Hpub]].
  - pose proof Hord as (k1 & k2' & pr & sw & Heq1 & Heq2 & Hfb).
    subst e1. assert (k2' = k2) as -> by (by simplify_eq).
    assert (Hex : ∃ s1, ex_tr (cand_exec (lin_cand G)) !! k1 = Some s1).
    { destruct Hfb as (kf & sf & s1 & s2' & _ & _ & Hs1 & _). by exists s1. }
    destruct Hex as [s1 Hs1].
    destruct (lin_tr_lookup_inv k1 s1 Hs1) as (e1 & Hk1 & _).
    assert (Hw1 : glbl_is G e1 lb_is_w).
    { apply (gis_w_glbl_is e1 (glin_lookup_lbl k1 e1 Hk1)).
      apply (lin_is_W k1 e1 Hk1), (proj1 Hpub). }
    assert (Hmo : gmo_lt G e1 e2).
    { apply Hppo. right. left. exists pr, true, true, sw. split_and!.
      - by eapply lin_fence_between.
      - by right.
      - by left. }
    by apply (lin_ord_core k1 k2 e1 e2 a w t Hk1 Hk2 Hmo (or_introl Hpub)).
  - pose proof Hpub as (k1 & s1 & a1 & v1 & Heq1 & Hs1 & Hr1 & _).
    subst e1.
    destruct (lin_tr_lookup_inv k1 s1 Hs1) as (e1 & Hk1 & _).
    assert (Hisr1 : glbl_is G e1 lb_is_r).
    { apply (greads_byte_is_r e1 a1 t v1).
      by apply (lin_reads_at k1 e1 a1 t v1 Hk1). }
    assert (Hmo : gmo_lt G e1 e2).
    { destruct Hord as [(n1 & n2 & pw & sw & Heq2 & Heq3 & Hfb)|Hacq].
      - simplify_eq. apply Hppo. right. left.
        exists true, pw, true, sw. split_and!.
        + by eapply lin_fence_between.
        + by left.
        + by left.
      - by apply (lin_acq_po_gmo k1 k2 e1 e2 Hk1 Hk2). }
    by apply (lin_ord_core k1 k2 e1 e2 a w t Hk1 Hk2 Hmo (or_intror Hpub)).
Qed.

Lemma lin_rel_ord : ax_rel_ord (cand_exec (lin_cand G)).
Proof.
  intros e1 k2 s2 a w t Hs2 Hrel Hpub Hfr.
  destruct (lin_read_at_2 k2 s2 a w Hs2 Hfr) as (e2 & Hk2 & _).
  pose proof Hpub as (HW & [k1 Hk1eq] & Hts). subst e1.
  assert (Hex : ∃ s1, ex_tr (cand_exec (lin_cand G)) !! k1 = Some s1)
    by (destruct HW as (s1 & Hs1 & _); by exists s1).
  destruct Hex as [s1 Hs1].
  destruct (lin_tr_lookup_inv k1 s1 Hs1) as (e1 & Hk1 & _).
  assert (Hmo : gmo_lt G e1 e2).
  { destruct Hrel as [Hra|(em & Hra & _ & Hacq)].
    - by apply (lin_rel_acq_gmo k1 k2 e1 e2 Hk1 Hk2).
    - pose proof Hacq as (n1 & n2 & sm & sm2 & Hem & Heq2 & _ & Hsm & _).
      subst em. assert (n2 = k2) as -> by (by simplify_eq).
      destruct (lin_tr_lookup_inv n1 sm Hsm) as (em & Hkm & _).
      apply (gmo_lt_trans G e1 em e2).
      + by apply (lin_rel_acq_gmo k1 n1 e1 em Hk1 Hkm).
      + by apply (lin_acq_po_gmo n1 k2 em e2 Hkm Hk2). }
  by apply (lin_ord_core k1 k2 e1 e2 a w t Hk1 Hk2 Hmo (or_introl Hpub)).
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 4.6 The per-agent program rows, and the whole log *)

Lemma filter_fmap_glin (l : list geid) i :
  filter (λ s : estep, es_ag s = i) (glin_step G <$> l)
  = glin_step G <$> filter (λ e : geid, e.1 = i) l.
Proof.
  induction l as [|e l IH]; [done|].
  rewrite fmap_cons !filter_cons.
  case_decide as H1; simpl in H1; case_decide as H2;
    [by rewrite fmap_cons IH|done|done|exact IH].
Qed.

Lemma lin_prog i :
  (λ s : estep, es_lb s) <$> filter (λ s : estep, es_ag s = i)
                                    (cd_tr (lin_cand G))
  = grow G i.
Proof.
  change (cd_tr (lin_cand G)) with (glin_step G <$> glin_eids G).
  rewrite filter_fmap_glin glin_hart /gevs_hart.
  apply list_eq. intros k. rewrite !list_lookup_fmap.
  destruct (decide (k < length (grow G i))%nat) as [Hk|Hk]; last first.
  { assert (Hs : seq 0 (length (grow G i)) !! k = None)
      by (apply lookup_seq_ge; lia).
    assert (Hg : grow G i !! k = None) by (apply lookup_ge_None_2; lia).
    by rewrite Hs Hg. }
  assert (Hs : seq 0 (length (grow G i)) !! k = Some k).
  { apply lookup_seq. split; [lia|exact Hk]. }
  rewrite Hs /=.
  assert (Hi : (i < length (gx_prog G))%nat).
  { destruct (decide (i < length (gx_prog G))%nat) as [?|Hge]; [done|].
    exfalso. rewrite /grow in Hk.
    destruct (gx_prog G !! i) as [p|] eqn:Hp;
      [apply lookup_lt_Some in Hp; lia|simpl in Hk; lia]. }
  assert (Hl : gx_lbl G (i, k) = grow G i !! k)
    by (rewrite /gx_lbl (grow_lookup G i Hi) //).
  destruct (grow G i !! k) as [l|] eqn:Hlk;
    [|exfalso; apply lookup_ge_None in Hlk; lia].
  by rewrite /glbl Hl.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 4.7 The section's theorem *)

Theorem lin_srvwmo : srvwmo_consistent (lin_cand G).
Proof.
  assert (Hwfe : exec_wf (cand_exec (lin_cand G))).
  { apply (promise_free_complete_local (lin_cand G) lin_shape lin_values
             (cand_rf_total (lin_cand G) lin_values) lin_coherence lin_ord
             lin_rel_ord lin_atomicity). }
  split_and!; [exact lin_shape|exact lin_values|split_and!].
  - by apply promise_free_sound.
  - by apply sound_rel_ord.
  - by apply promise_free_ob_acyclic.
Qed.

End lin.

(* ====================================================================== *)
(** * 5. THE RULE-14 LINEARIZATION *)

Theorem rule14_linearization G :
  rvwmo_minus_consistent G → grule14 G →
  ∃ c : cand,
    srvwmo_consistent c ∧
    cd_img c = gx_img G ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = default [] (gx_prog G !! i)) ∧
    cd_log c (length (cd_tr c)) = omap (gmsg G) (gwrites G).
Proof.
  intros (Hwf & Hppo & Hlv & Hat) H14.
  exists (lin_cand G). split_and!.
  - apply lin_srvwmo; assumption.
  - done.
  - intros i. apply lin_prog; assumption.
  - apply lin_full_log; assumption.
Qed.
