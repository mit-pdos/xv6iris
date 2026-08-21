(** * WeakRvwmoRestr.v — THE RESTRICTION SLICE (route B, stage B1a)

    Design: [claude-notes/design/weak-memory-route-b.md] §4b.

    THE POINT.  The exchange normalization ([WeakRvwmoNorm.normalize]) hands
    its kill interface a po-MINIMAL violating witness [e] below a
    gmo-MINIMAL violating write [w].  Minimality makes the events strictly
    below the frontier a DOUBLY CLOSED prefix — closed under [gpo] within
    each hart, and closed downwards in [gmo] — and B1b realizes exactly that
    prefix as a promise-free machine run.  This file is the order-theoretic
    half: cutting a graph down to such a prefix PRESERVES RVWMO⁻
    consistency, and — when the prefix is violation-free, which is what
    minimality supplies — the cut graph satisfies rule 14 and therefore
    LINEARIZES by the landed [WeakRvwmoLin.rule14_linearization].

    THE OBJECT.  [gx_restrict G cs n] cuts each program row [i] at [cs !! i]
    and the global memory order at [n]; [restr_ok] ties the two — an event
    survives the per-hart cut iff (mem case) it survives the gmo cut.  With
    that one tie every restriction lemma is bookkeeping:

      - the LABEL of a restricted event is [G]'s label below the cut and
        [None] above it ([gxr_lbl]) — so every label-determined notion
        ([gmem], [gis_w], [gpo], the byte footprints, [gmsg]) restricts by
        conjunction with the cut predicate [gcut];
      - the gmo prefix is a literal [take], so [gpos] is PRESERVED for its
        members ([gxr_gpos]) and gmo-down-closure is free;
      - [gwrites] of the restriction is [filter (gis_w G) (take n …)]
        ([gwrites_restrict]), a PREFIX of [gwrites G] ([gwpre_app]) — hence
        [gwix] agrees below the cut ([gxr_gwix]) and a read's [ts] entry is
        reused verbatim, exactly as in the linearization.

    WHAT IS PROVED: [restrict_consistent], [restrict_rule14],
    [restrict_deps_consistent], and the composition [restrict_linearizes].

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2 WeakAxiomatic3
                            WeakRvwmoGraph WeakRvwmoLin WeakRvwmoXchg.

(* ====================================================================== *)
(** * 1. A GENERIC LIST KIT *)

(** [filter] only looks at the list's own elements. *)
Lemma filter_iff_elem {A} (P Q : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} (l : list A) :
  (∀ x, x ∈ l → (P x ↔ Q x)) → filter P l = filter Q l.
Proof.
  induction l as [|x l IH]; intros Hiff; [by rewrite !filter_nil|].
  assert (Hx : P x ↔ Q x) by (apply Hiff, elem_of_list_here).
  assert (Hrest : ∀ y, y ∈ l → (P y ↔ Q y))
    by (intros y Hy; apply Hiff, elem_of_list_further, Hy).
  rewrite !filter_cons. case_decide as Hp; case_decide as Hq.
  - by rewrite (IH Hrest).
  - by destruct Hq; apply Hx.
  - by destruct Hp; apply Hx.
  - by rewrite (IH Hrest).
Qed.

Lemma take_NoDup {A} (l : list A) m : NoDup l → NoDup (take m l).
Proof.
  rewrite !NoDup_alt. intros Hnd i j x Hi Hj.
  apply lookup_take_Some in Hi as [Hi _].
  apply lookup_take_Some in Hj as [Hj _]. by eapply Hnd.
Qed.

(* ====================================================================== *)
(** * 2. THE CUT PREDICATE AND THE RESTRICTED GRAPH *)

(** [gcut cs e]: [e] survives its hart's row cut.  A BOOLEAN — the
    restriction filters with it, and the import context does not elaborate
    [if decide _ then _ else _] (durable-notes). *)
Definition gcut (cs : list nat) (e : geid) : bool :=
  match cs !! e.1 with
  | Some c => bool_decide (e.2 < c)%nat
  | None => false
  end.

Lemma gcut_intro cs e c : cs !! e.1 = Some c → (e.2 < c)%nat → gcut cs e = true.
Proof. intros Hc Hlt. rewrite /gcut Hc. by apply bool_decide_eq_true. Qed.

Lemma gcut_elim cs e :
  gcut cs e = true → ∃ c, cs !! e.1 = Some c ∧ (e.2 < c)%nat.
Proof.
  rewrite /gcut. destruct (cs !! e.1) as [c|] eqn:Hc; [|done].
  intros Hd%bool_decide_eq_true. by exists c.
Qed.

(** THE CUT IS PO-DOWN-CLOSED — the reason po-closure of the prefix needs no
    separate clause in [restr_ok]. *)
Lemma gcut_po_down cs e1 e2 :
  e1.1 = e2.1 → (e1.2 < e2.2)%nat → gcut cs e2 = true → gcut cs e1 = true.
Proof.
  intros Hag Hlt Hc. apply gcut_elim in Hc as (c & Hc & Hlt2).
  apply (gcut_intro cs e1 c); [by rewrite Hag|lia].
Qed.

(** THE OBJECT: per-hart row cuts [cs] plus a gmo cut [n]. *)
Definition gx_restrict (G : gexec) (cs : list nat) (n : nat) : gexec :=
  GExec (gx_img G)
        (zip_with take cs (gx_prog G))
        (take n (gx_gmo G)).

(** [restr_ok]: the cuts' MEM events are exactly the gmo prefix.
    (SHAPE NOTE — the iff of the design is split into its two inclusions,
    and the [gmem] guard is dropped on the ⇐ side: a member of the gmo
    prefix is a mem event anyway under [gwf], and the unguarded form is
    what every consumer applies.  The CONTENT is the design's.) *)
Definition restr_ok (G : gexec) (cs : list nat) (n : nat) : Prop :=
  length cs = length (gx_prog G) ∧
  (∀ e, gmem G e → gcut cs e = true → e ∈ take n (gx_gmo G)) ∧
  (∀ e, e ∈ take n (gx_gmo G) → gcut cs e = true).

Lemma restr_ok_len G cs n : restr_ok G cs n → length cs = length (gx_prog G).
Proof. by intros (? & _ & _). Qed.

Lemma restr_ok_in G cs n e :
  restr_ok G cs n → gmem G e → gcut cs e = true → e ∈ take n (gx_gmo G).
Proof. intros (_ & H & _) Hm Hc. by apply H. Qed.

Lemma restr_ok_cut G cs n e :
  restr_ok G cs n → e ∈ take n (gx_gmo G) → gcut cs e = true.
Proof. intros (_ & _ & H) He. by apply H. Qed.

(* ====================================================================== *)
(** * 3. THE LABEL LAYER: everything label-determined restricts by [gcut] *)

Lemma gxr_prog_lookup G cs n i :
  gx_prog (gx_restrict G cs n) !! i
  = (c ← cs !! i; p ← gx_prog G !! i; Some (take c p)).
Proof. by rewrite /gx_restrict /= lookup_zip_with. Qed.

(** The row of the restriction, in the shape [restrict_linearizes] reports. *)
Lemma gxr_row G cs n i :
  default [] (gx_prog (gx_restrict G cs n) !! i)
  = take (default 0%nat (cs !! i)) (default [] (gx_prog G !! i)).
Proof.
  rewrite gxr_prog_lookup.
  destruct (cs !! i) as [c|] eqn:Hc; destruct (gx_prog G !! i) as [p|] eqn:Hp;
    by rewrite /= ?take_nil.
Qed.

(** THE LABEL EQUATION. *)
Lemma gxr_lbl G cs n e :
  gx_lbl (gx_restrict G cs n) e = if gcut cs e then gx_lbl G e else None.
Proof.
  rewrite /gx_lbl gxr_prog_lookup /gcut.
  destruct (cs !! e.1) as [c|] eqn:Hc; [|done].
  destruct (gx_prog G !! e.1) as [p|] eqn:Hp; simpl.
  - case_bool_decide as Hlt.
    + rewrite lookup_take; [done|done].
    + rewrite lookup_take_ge; [lia|done].
  - by case_bool_decide.
Qed.

Lemma gxr_lbl_in G cs n e :
  gcut cs e = true → gx_lbl (gx_restrict G cs n) e = gx_lbl G e.
Proof. intros Hc. by rewrite gxr_lbl Hc. Qed.

Lemma gxr_lbl_Some G cs n e l :
  gx_lbl (gx_restrict G cs n) e = Some l →
  gcut cs e = true ∧ gx_lbl G e = Some l.
Proof. rewrite gxr_lbl. by destruct (gcut cs e). Qed.

Lemma gxr_is_Some G cs n e :
  is_Some (gx_lbl (gx_restrict G cs n) e) ↔ gcut cs e = true ∧ is_Some (gx_lbl G e).
Proof.
  split.
  - intros [l Hl%gxr_lbl_Some]. destruct Hl as [Hc Hl]. split; [done|by exists l].
  - intros (Hc & [l Hl]). exists l. by rewrite gxr_lbl_in.
Qed.

Lemma gxr_glbl_is G cs n e P :
  glbl_is (gx_restrict G cs n) e P ↔ gcut cs e = true ∧ glbl_is G e P.
Proof.
  rewrite /glbl_is. split.
  - intros (l & Hl%gxr_lbl_Some & HP). destruct Hl as [Hc Hl].
    split; [done|by exists l].
  - intros (Hc & (l & Hl & HP)). exists l. by rewrite gxr_lbl_in.
Qed.

Lemma gxr_gmem G cs n e :
  gmem (gx_restrict G cs n) e ↔ gcut cs e = true ∧ gmem G e.
Proof.
  rewrite /gmem. split.
  - intros (l & Hl%gxr_lbl_Some & Hm). destruct Hl as [Hc Hl].
    split; [done|by exists l].
  - intros (Hc & (l & Hl & Hm)). exists l. by rewrite gxr_lbl_in.
Qed.

Lemma gxr_gis_w G cs n e :
  gis_w (gx_restrict G cs n) e = if gcut cs e then gis_w G e else false.
Proof. rewrite /gis_w gxr_lbl. by destruct (gcut cs e). Qed.

Lemma gxr_gis_w_true G cs n e :
  gis_w (gx_restrict G cs n) e = true ↔ gcut cs e = true ∧ gis_w G e = true.
Proof. rewrite gxr_gis_w. destruct (gcut cs e); naive_solver. Qed.

(** [gpo] restricts by the cut of its TARGET — the source follows by
    [gcut_po_down]. *)
Lemma gxr_gpo G cs n e1 e2 :
  gpo (gx_restrict G cs n) e1 e2 ↔ gpo G e1 e2 ∧ gcut cs e2 = true.
Proof.
  rewrite /gpo !gxr_is_Some. split.
  - intros (Hag & Hlt & (Hc1 & Hs1) & (Hc2 & Hs2)). split_and!; done.
  - intros ((Hag & Hlt & Hs1 & Hs2) & Hc2). split_and!; try done.
    by eapply gcut_po_down.
Qed.

Lemma gxr_wrb G cs n e a v :
  gwrites_byte (gx_restrict G cs n) e a v ↔ gcut cs e = true ∧ gwrites_byte G e a v.
Proof.
  rewrite /gwrites_byte. split.
  - intros (l & base & vs & j & Hl%gxr_lbl_Some & Hrest). destruct Hl as [Hc Hl].
    split; [done|]. by exists l, base, vs, j.
  - intros (Hc & (l & base & vs & j & Hl & Hrest)).
    exists l, base, vs, j. by rewrite gxr_lbl_in.
Qed.

Lemma gxr_rdb G cs n e a t v :
  greads_byte (gx_restrict G cs n) e a t v ↔ gcut cs e = true ∧ greads_byte G e a t v.
Proof.
  rewrite /greads_byte. split.
  - intros (l & base & ts & vs & j & Hl%gxr_lbl_Some & Hrest).
    destruct Hl as [Hc Hl]. split; [done|]. by exists l, base, ts, vs, j.
  - intros (Hc & (l & base & ts & vs & j & Hl & Hrest)).
    exists l, base, ts, vs, j. by rewrite gxr_lbl_in.
Qed.

Lemma gxr_gaccesses G cs n e a :
  gaccesses (gx_restrict G cs n) e a → gaccesses G e a.
Proof.
  intros [(v & Hw%gxr_wrb)|(t & v & Hr%gxr_rdb)];
    [left; exists v|right; exists t, v]; naive_solver.
Qed.

Lemma gxr_gmsg G cs n e :
  gcut cs e = true → gmsg (gx_restrict G cs n) e = gmsg G e.
Proof. intros Hc. by rewrite /gmsg gxr_lbl_in. Qed.

(** The two "this byte footprint makes the event a memory event" bridges. *)
Lemma wrb_gmem G e a v : gwrites_byte G e a v → gmem G e.
Proof.
  intros Hw. pose proof (gwrites_byte_gis_w G e a v Hw) as Hisw.
  destruct Hw as (l & base & vs & j & Hl & _). exists l. split; [done|].
  rewrite /gis_w Hl in Hisw. by rewrite /lb_is_mem Hisw orb_true_r.
Qed.

Lemma rdb_gmem G e a t v : greads_byte G e a t v → gmem G e.
Proof.
  intros (l & base & ts & vs & j & Hl & Hrd & _). exists l. split; [done|].
  by rewrite /lb_is_mem (lb_rd_is_r l _ Hrd).
Qed.

Lemma glbl_is_w_gmem G e : glbl_is G e lb_is_w → gmem G e.
Proof.
  intros (l & Hl & Hw). exists l. split; [done|].
  by rewrite /lb_is_mem Hw orb_true_r.
Qed.

Lemma glbl_is_r_gmem G e : glbl_is G e lb_is_r → gmem G e.
Proof.
  intros (l & Hl & Hr). exists l. split; [done|]. by rewrite /lb_is_mem Hr.
Qed.

(** EVERY ppo⁻ ARM PINS BOTH ENDPOINTS' LABELS — so a ppo⁻ edge of the
    restriction has both ends inside the cut. *)
Lemma gppo_lbl G e1 e2 :
  gppo G e1 e2 → is_Some (gx_lbl G e1) ∧ is_Some (gx_lbl G e2).
Proof.
  intros [[(_ & _ & H1 & H2) _]
         |[(pr & pw & sr & sw & _ & Hk1 & Hk2)
          |[[(_ & _ & H1 & H2) _]|[(_ & _ & H1 & H2) _]]]]; try done.
  split.
  - destruct Hk1 as [[(l & Hl & _) _]|[(l & Hl & _) _]]; by exists l.
  - destruct Hk2 as [[(l & Hl & _) _]|[(l & Hl & _) _]]; by exists l.
Qed.

(** THE ppo⁻ TRANSFER: an edge of the restriction is an edge of [G]. *)
Lemma gxr_gppo G cs n e1 e2 :
  gppo (gx_restrict G cs n) e1 e2 → gppo G e1 e2.
Proof.
  intros [Hpl|[Hf|[Ha|Hr]]].
  - left. destruct Hpl as (Hpo%gxr_gpo & a & H1 & H2).
    split; [by destruct Hpo|]. exists a. split; by eapply gxr_gaccesses.
  - right; left. destruct Hf as (pr & pw & sr & sw & Hfb & Hk1 & Hk2).
    exists pr, pw, sr, sw. split_and!.
    + destruct Hfb as (Hag & Hlt & kf & Hk3 & Hk4 & Hlf%gxr_lbl_Some).
      split_and!; [done|done|]. exists kf. split_and!; [done|done|by destruct Hlf].
    + destruct Hk1 as [[H%gxr_glbl_is ?]|[H%gxr_glbl_is ?]];
        [left|right]; (split; [by destruct H|done]).
    + destruct Hk2 as [[H%gxr_glbl_is ?]|[H%gxr_glbl_is ?]];
        [left|right]; (split; [by destruct H|done]).
  - right; right; left.
    destruct Ha as (Hpo%gxr_gpo & H1%gxr_glbl_is & H2%gxr_glbl_is
                    & H3%gxr_gmem).
    split_and!; [by destruct Hpo|by destruct H1|by destruct H2
                |by destruct H3].
  - right; right; right.
    destruct Hr as (Hpo%gxr_gpo & H1%gxr_glbl_is & H2%gxr_glbl_is
                    & H3%gxr_glbl_is & H4%gxr_glbl_is).
    split_and!; [by destruct Hpo|by destruct H1|by destruct H2
                |by destruct H3|by destruct H4].
Qed.

Lemma gxr_gppo_cut G cs n e1 e2 :
  gppo (gx_restrict G cs n) e1 e2 → gcut cs e1 = true ∧ gcut cs e2 = true.
Proof.
  intros Hppo. destruct (gppo_lbl _ _ _ Hppo) as [H1 H2].
  apply gxr_is_Some in H1 as [Hc1 _]. apply gxr_is_Some in H2 as [Hc2 _]. done.
Qed.

(* ====================================================================== *)
(** * 4. THE GMO PREFIX: positions are PRESERVED *)

Lemma take_elem_gmo G n e : e ∈ take n (gx_gmo G) → e ∈ gx_gmo G.
Proof.
  intros He. apply elem_of_take in He as (i & Hi & _).
  by eapply elem_of_list_lookup_2.
Qed.

Lemma gxr_gpos G cs n e :
  NoDup (gx_gmo G) → e ∈ take n (gx_gmo G) →
  gpos (gx_restrict G cs n) e = gpos G e.
Proof.
  intros Hnd He.
  destruct (gpos_lookup (gx_restrict G cs n) e He) as (i & Hi & ->).
  simpl in Hi. apply lookup_take_Some in Hi as [Hi _].
  symmetry. by apply gpos_of_lookup.
Qed.

Lemma gpos_take_lt G n e :
  NoDup (gx_gmo G) → e ∈ take n (gx_gmo G) → (gpos G e < n)%nat.
Proof.
  intros Hnd He. apply elem_of_take in He as (i & Hi & Hlt).
  by rewrite (gpos_of_lookup G i e Hnd Hi).
Qed.

Lemma gpos_lt_take G n e :
  e ∈ gx_gmo G → (gpos G e < n)%nat → e ∈ take n (gx_gmo G).
Proof.
  intros He Hlt. apply elem_of_take. exists (gpos G e).
  split; [by apply gpos_elem_lookup|done].
Qed.

Lemma gxr_gmo_lt G cs n e1 e2 :
  NoDup (gx_gmo G) →
  gmo_lt (gx_restrict G cs n) e1 e2
  ↔ e1 ∈ take n (gx_gmo G) ∧ e2 ∈ take n (gx_gmo G) ∧ gmo_lt G e1 e2.
Proof.
  intros Hnd. split.
  - intros (H1 & H2 & Hlt). simpl in H1, H2.
    rewrite (gxr_gpos G cs n e1 Hnd H1) (gxr_gpos G cs n e2 Hnd H2) in Hlt.
    split_and!; [done|done|]. split_and!; by [eapply take_elem_gmo|].
  - intros (H1 & H2 & (_ & _ & Hlt)). split_and!; [exact H1|exact H2|].
    by rewrite (gxr_gpos G cs n e1 Hnd H1) (gxr_gpos G cs n e2 Hnd H2).
Qed.

(* ====================================================================== *)
(** * 5. THE WRITE SUB-ORDER: a PREFIX of [gwrites G] *)

(** The restriction's write sub-order, spelled without the restriction. *)
Definition gwpre (G : gexec) (n : nat) : list geid :=
  filter (gis_w G) (take n (gx_gmo G)).

Lemma gwrites_restrict G cs n :
  (∀ e, e ∈ take n (gx_gmo G) → gcut cs e = true) →
  gwrites (gx_restrict G cs n) = gwpre G n.
Proof.
  intros Hcut. rewrite /gwrites /gwpre /=.
  apply filter_iff_elem. intros e He.
  by rewrite gxr_gis_w (Hcut e He).
Qed.

Lemma gwpre_app G n :
  gwrites G = gwpre G n ++ filter (gis_w G) (drop n (gx_gmo G)).
Proof.
  rewrite /gwpre /gwrites -list_basics.filter_app take_drop //.
Qed.

Lemma gwpre_lookup G n i w : gwpre G n !! i = Some w → gwrites G !! i = Some w.
Proof. intros Hi. rewrite (gwpre_app G n). by apply lookup_app_l_Some. Qed.

Lemma gwpre_take G n : gwpre G n = take (length (gwpre G n)) (gwrites G).
Proof. by rewrite (gwpre_app G n) take_app_length. Qed.

Lemma gwpre_elem G n w : w ∈ gwpre G n → w ∈ take n (gx_gmo G).
Proof. rewrite /gwpre elem_of_list_filter. by intros [_ ?]. Qed.

Lemma gxr_gwrites_in G cs n w :
  gcut cs w = true → w ∈ take n (gx_gmo G) → gis_w G w = true →
  w ∈ gwrites (gx_restrict G cs n).
Proof.
  intros Hc Hm Hw. apply gwrites_elem_of. split; [exact Hm|].
  by apply gxr_gis_w_true.
Qed.

Lemma gxr_gwrites_out G cs n w :
  w ∈ gwrites (gx_restrict G cs n) →
  gcut cs w = true ∧ w ∈ take n (gx_gmo G) ∧ gis_w G w = true.
Proof.
  intros [Hm Hw%gxr_gis_w_true]%gwrites_elem_of. simpl in Hm. naive_solver.
Qed.

Lemma gxr_gwix G cs n w :
  NoDup (gx_gmo G) → (∀ e, e ∈ take n (gx_gmo G) → gcut cs e = true) →
  w ∈ gwrites (gx_restrict G cs n) →
  gwix (gx_restrict G cs n) w = gwix G w.
Proof.
  intros Hnd Hcut Hw.
  destruct (gwix_lookup (gx_restrict G cs n) w Hw) as (i & Hi & ->).
  rewrite (gwrites_restrict G cs n Hcut) in Hi.
  symmetry. by apply (gwix_of_lookup G i w Hnd (gwpre_lookup G n i w Hi)).
Qed.

Lemma gxr_gwrite_at G cs n t w :
  (∀ e, e ∈ take n (gx_gmo G) → gcut cs e = true) →
  gwrite_at (gx_restrict G cs n) t = Some w → gwrite_at G t = Some w.
Proof.
  intros Hcut Ht. destruct t as [|i]; [done|].
  rewrite /gwrite_at (gwrites_restrict G cs n Hcut) in Ht.
  by apply (gwpre_lookup G n i w Ht).
Qed.

Lemma gxr_gwrite_at_in G cs n t w :
  NoDup (gx_gmo G) → (∀ e, e ∈ take n (gx_gmo G) → gcut cs e = true) →
  w ∈ gwrites (gx_restrict G cs n) → gwrite_at G t = Some w →
  gwrite_at (gx_restrict G cs n) t = Some w.
Proof.
  intros Hnd Hcut Hw Ht.
  destruct (gwrite_at_inv G t w Hnd Ht) as (_ & <-).
  rewrite -(gxr_gwix G cs n w Hnd Hcut Hw). by apply gwrite_at_gwix.
Qed.

(* ====================================================================== *)
(** * 6. CONSISTENCY RESTRICTS *)

Theorem restrict_consistent G cs n :
  rvwmo_minus_consistent G → restr_ok G cs n →
  rvwmo_minus_consistent (gx_restrict G cs n).
Proof.
  intros (Hwf & Hppo & Hlv & Hat) Hro.
  pose proof Hwf as (Hnd & Hmem & Hsh).
  pose proof (restr_ok_cut G cs n) as Hcut'.
  assert (Hcut : ∀ e, e ∈ take n (gx_gmo G) → gcut cs e = true)
    by (intros e He; by eapply restr_ok_cut).
  (* the two "an in-cut memory event is in the prefix" shapes, once *)
  assert (Hin : ∀ e, gcut cs e = true → gmem G e → e ∈ take n (gx_gmo G))
    by (intros e Hc Hm; by eapply restr_ok_in).
  split_and!.
  - (* gwf *) split_and!.
    + by apply take_NoDup.
    + intros e. rewrite gxr_gmem. split.
      * intros He. split; [by apply Hcut|].
        by apply Hmem, take_elem_gmo with n.
      * intros [Hc Hm]. by apply Hin.
    + intros i p k l Hp Hk.
      rewrite gxr_prog_lookup in Hp.
      destruct (cs !! i) as [c|] eqn:Hc; [|done].
      destruct (gx_prog G !! i) as [p0|] eqn:Hp0; [|done].
      simpl in Hp. simplify_eq.
      apply lookup_take_Some in Hk as [Hk _]. by eapply Hsh.
  - (* gppo⁻ ⊆ gmo *)
    intros e1 e2 Hppo'.
    destruct (gxr_gppo_cut G cs n e1 e2 Hppo') as [Hc1 Hc2].
    pose proof (Hppo e1 e2 (gxr_gppo G cs n e1 e2 Hppo')) as Hmo.
    pose proof Hmo as (Hg1 & Hg2 & _).
    apply gxr_gmo_lt; [done|]. split_and!; [| |done];
      apply Hin; by [|apply Hmem].
  - (* load value *)
    intros e a t v [Hce Hrd]%gxr_rdb.
    assert (He : e ∈ take n (gx_gmo G)) by (apply Hin; [done|by eapply rdb_gmem]).
    destruct (Hlv e a t v Hrd) as [Hsrc Hmax].
    split.
    + destruct t as [|t]; [exact Hsrc|].
      destruct Hsrc as (w & Hwat & Hwb & Hvis).
      assert (Hwm : w ∈ take n (gx_gmo G)).
      { destruct Hvis as [Hmo|Hpo].
        - apply gpos_lt_take; [by destruct Hmo as (?&?&?)|].
          destruct Hmo as (_ & _ & Hlt).
          pose proof (gpos_take_lt G n e Hnd He). lia.
        - apply Hin; [|by eapply wrb_gmem].
          destruct Hpo as (Hag & Hlt & _). by eapply gcut_po_down. }
      assert (Hcw : gcut cs w = true) by by apply Hcut.
      assert (Hwg : w ∈ gwrites (gx_restrict G cs n)).
      { apply gxr_gwrites_in; [done|done|].
        by eapply gwrites_byte_gis_w. }
      exists w. split_and!.
      * by apply gxr_gwrite_at_in.
      * by apply gxr_wrb.
      * destruct Hvis as [Hmo|Hpo]; [left|right].
        { by apply gxr_gmo_lt. }
        { by apply gxr_gpo. }
    + intros w' v' [Hcw' Hwb']%gxr_wrb Hvis'.
      assert (Hwm' : w' ∈ take n (gx_gmo G))
        by (apply Hin; [done|by eapply wrb_gmem]).
      assert (Hwg' : w' ∈ gwrites (gx_restrict G cs n)).
      { apply gxr_gwrites_in; [done|done|by eapply gwrites_byte_gis_w]. }
      rewrite (gxr_gwix G cs n w' Hnd Hcut Hwg').
      apply (Hmax w' v' Hwb').
      destruct Hvis' as [Hmo|Hpo]; [left|right].
      * by apply (gxr_gmo_lt G cs n w' e Hnd) in Hmo as (_ & _ & ?).
      * by apply gxr_gpo in Hpo as [? _].
  - (* atomicity *)
    intros e a t v [Hce Hrd]%gxr_rdb [_ Hw]%gxr_glbl_is w' v' [Hcw' Hwb']%gxr_wrb.
    assert (He : e ∈ take n (gx_gmo G))
      by (apply Hin; [done|by eapply rdb_gmem]).
    assert (Hwm' : w' ∈ take n (gx_gmo G))
      by (apply Hin; [done|by eapply wrb_gmem]).
    assert (Heg : e ∈ gwrites (gx_restrict G cs n)).
    { apply gxr_gwrites_in; [done|done|by eapply glbl_is_w_gis_w]. }
    assert (Hwg' : w' ∈ gwrites (gx_restrict G cs n)).
    { apply gxr_gwrites_in; [done|done|by eapply gwrites_byte_gis_w]. }
    rewrite (gxr_gwix G cs n w' Hnd Hcut Hwg') (gxr_gwix G cs n e Hnd Hcut Heg).
    by apply (Hat e a t v Hrd Hw w' v' Hwb').
Qed.

(* ====================================================================== *)
(** * 7. RULE 14 FROM VIOLATION-FREEDOM OF THE CUT *)

(** A violation of the restriction is one of [G], with both ends in the cut. *)
Lemma gviol_restrict G cs n e w :
  NoDup (gx_gmo G) → gviol (gx_restrict G cs n) e w →
  gviol G e w ∧ gcut cs e = true ∧ gcut cs w = true.
Proof.
  intros Hnd (Hpo & Hme & Hw & Hmo).
  apply gxr_gpo in Hpo as [Hpo Hcw].
  apply gxr_gmem in Hme as [Hce Hme].
  apply gxr_glbl_is in Hw as [_ Hw].
  apply (gxr_gmo_lt G cs n w e Hnd) in Hmo as (_ & _ & Hmo).
  by split_and!.
Qed.

Theorem restrict_rule14 G cs n :
  rvwmo_minus_consistent G → restr_ok G cs n →
  (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol G e w) →
  grule14 (gx_restrict G cs n).
Proof.
  intros Hc Hro Hvf. pose proof Hc as (Hwf & _ & _). pose proof Hwf as (Hnd & _).
  apply gviol_grule14.
  - by apply (restrict_consistent G cs n Hc Hro).
  - intros e w Hv.
    destruct (gviol_restrict G cs n e w Hnd Hv) as (Hv' & Hce & Hcw).
    by apply (Hvf e w Hce Hcw).
Qed.

(* ====================================================================== *)
(** * 8. THE [gdexec] FORM: the dep fragment restricts by filtering *)

Definition gd_restrict (GD : gdexec) (cs : list nat) (n : nat) : gdexec :=
  GDExec (gx_restrict (gd_g GD) cs n)
         (filter (λ rw : geid * geid, gcut cs rw.1 && gcut cs rw.2)
                 (gd_deps GD)).

Lemma gd_restrict_deps GD cs n rw :
  rw ∈ gd_deps (gd_restrict GD cs n) ↔
  rw ∈ gd_deps GD ∧ gcut cs rw.1 = true ∧ gcut cs rw.2 = true.
Proof.
  rewrite /gd_restrict /= elem_of_list_filter Is_true_true andb_true_iff.
  naive_solver.
Qed.

Theorem restrict_deps_consistent GD cs n :
  rvwmo_minus_deps_consistent GD → restr_ok (gd_g GD) cs n →
  rvwmo_minus_deps_consistent (gd_restrict GD cs n).
Proof.
  intros (Hc & Hdwf & Hdmo) Hro.
  pose proof Hc as (Hwf & _ & _). pose proof Hwf as (Hnd & Hmem & _).
  split_and!.
  - by apply restrict_consistent.
  - intros rw [Hrw [Hc1 Hc2]]%gd_restrict_deps.
    destruct (Hdwf rw Hrw) as (H1 & H2 & H3 & H4).
    split_and!; [done|done|by apply gxr_glbl_is|by apply gxr_glbl_is].
  - intros rw [Hrw [Hc1 Hc2]]%gd_restrict_deps.
    destruct (Hdwf rw Hrw) as (_ & _ & H3 & H4).
    pose proof (Hdmo rw Hrw) as Hmo.
    apply gxr_gmo_lt; [done|]. split_and!; [| |done].
    + eapply restr_ok_in; [done|by eapply glbl_is_r_gmem|done].
    + eapply restr_ok_in; [done|by eapply glbl_is_w_gmem|done].
Qed.

(* ====================================================================== *)
(** * 9. THE COMPOSITION: a violation-free restriction LINEARIZES *)

Lemma omap_gmsg_cut G cs n (l : list geid) :
  (∀ e, e ∈ l → gcut cs e = true) →
  omap (gmsg (gx_restrict G cs n)) l = omap (gmsg G) l.
Proof.
  induction l as [|e l IH]; intros Hcut; [done|].
  assert (Hrest : ∀ x, x ∈ l → gcut cs x = true)
    by (intros x Hx; by apply Hcut, elem_of_list_further).
  csimpl. rewrite (gxr_gmsg G cs n e (Hcut e (elem_of_list_here _ _))).
  destruct (gmsg G e); by rewrite (IH Hrest).
Qed.

(** THE B2e-FACING COROLLARY.  A violation-free [restr_ok] restriction of a
    consistent [gdexec] is realized by a candidate: same image, the CUT rows,
    and the log is the prefix's writes' messages. *)
Theorem restrict_linearizes GD cs n :
  rvwmo_minus_deps_consistent GD → restr_ok (gd_g GD) cs n →
  (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol (gd_g GD) e w) →
  ∃ c : cand,
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g GD) ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = take (default 0%nat (cs !! i)) (default [] (gx_prog (gd_g GD) !! i))) ∧
    cd_log c (length (cd_tr c)) = omap (gmsg (gd_g GD)) (gwpre (gd_g GD) n).
Proof.
  intros HD Hro Hvf. pose proof HD as (Hc & _ & _).
  assert (Hcut : ∀ e, e ∈ take n (gx_gmo (gd_g GD)) → gcut cs e = true)
    by (intros e He; by eapply restr_ok_cut).
  destruct (rule14_linearization (gx_restrict (gd_g GD) cs n)
              (restrict_consistent _ _ _ Hc Hro)
              (restrict_rule14 _ _ _ Hc Hro Hvf))
    as (c & Hsr & Himg & Hrow & Hlog).
  exists c. split_and!; [done|exact Himg| |].
  - intros i. by rewrite (Hrow i) gxr_row.
  - rewrite Hlog (gwrites_restrict _ cs n Hcut).
    apply omap_gmsg_cut. intros e He. by apply Hcut, gwpre_elem.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 9.1 NON-VACUITY: the FULL cut IS a [restr_ok] restriction, and it is
    the identity — so [restr_ok] is satisfiable and [gcut] is not
    accidentally empty. *)

Definition gfull_cs (G : gexec) : list nat := length <$> gx_prog G.

Lemma gx_restrict_full G : gx_restrict G (gfull_cs G) (length (gx_gmo G)) = G.
Proof.
  destruct G as [img prog gmo]. rewrite /gx_restrict /gfull_cs /= take_ge //.
  f_equal. induction prog as [|p prog IH]; [done|].
  by rewrite fmap_cons /= take_ge // IH.
Qed.

Lemma restr_ok_full G : gwf G → restr_ok G (gfull_cs G) (length (gx_gmo G)).
Proof.
  intros Hwf. pose proof Hwf as (_ & Hmem & _).
  assert (Hid : take (length (gx_gmo G)) (gx_gmo G) = gx_gmo G) by (rewrite take_ge //).
  split_and!.
  - by rewrite /gfull_cs length_fmap.
  - intros e Hm _. rewrite Hid. by apply Hmem.
  - intros e He. rewrite Hid in He.
    destruct (proj1 (Hmem e) He) as (l & Hl & _). rewrite /gx_lbl in Hl.
    destruct (gx_prog G !! e.1) as [p|] eqn:Hp; simpl in Hl; [|done].
    apply (gcut_intro _ _ (length p)).
    + by rewrite /gfull_cs list_lookup_fmap Hp.
    + by eapply lookup_lt_Some.
Qed.
