(** * WeakRvwmoLin2.v — T2-1c′, THE TRACE-FLEXIBLE LINEARIZATION

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.4, the
    "B1b-2 RESIDUE LANDED … T2-1c′" paragraph; the enumerated obligations
    are [WeakRvwmoFloor.v] §10 (O1, O2, O6).

    THE PROBLEM T2-1c LEFT OPEN.  [WeakRvwmoLin.rule14_linearization]
    linearizes a rule-14 graph along ONE trace — the RANK trace
    [glin_eids] — and its proof is declarative in that trace.  B1b-2 found
    that this is not enough: a device bundle's fabric order is an
    ADDITIONAL constraint on the trace, so the linearization must accept
    ANY trace that respects the graph, not the one the rank happens to
    produce.  T2-1c′ is that theorem.

    THE ORDER A TRACE MUST RESPECT is [ptrace_rel] = po ∪ rf ∪ gmo|W:
    program order, the reads-from edges, and gmo RESTRICTED TO WRITES.
    Nothing more.  In particular gmo between a write and a READ is NOT
    imposed — SB-both-0 has each hart's read gmo-after the other hart's
    store yet linearizes, because the candidate machine's load value is
    COHERENCE-based (a read may sit anywhere between its source and its
    hart's next write), not position-based.  That freedom is exactly what
    [WeakRvwmoFloor] discharges operationally.

    A trace is a list of ALL program events — fences included.  So the
    carrier is [WeakRvwmoNorm.gevs'] (every labelled row position), not
    [gx_gmo] (the memory events); note [gevs' G = gevs G] definitionally,
    which is what lets [WeakRvwmoLin]'s row bookkeeping be reused.

    NO RENAMING.  A cand read's [ts] entry is a LOG index, and the log of
    a G-trace prefix is the gmo prefix ([gtp_wix]/[gtp_log]) — so the log
    index of a write IS its [gwix], for EVERY [ptrace_ext] trace, not just
    the rank one.  §2's [tw_count] is that fact; it is why the labels go
    across unchanged.

    WHAT IS IN THIS FILE.

      §1  list/order plumbing ([before] from a lookup pair, counting).
      §2  [ptrace_rel] / [ptrace_ext] / [cand_of].
      §3  THE STEP (O3–O6): one generic snoc lemma over all four labels;
          the RMW's [rmw_latest] (O6) is [gatomicity] read through the log
          dictionary — see the note at [gtrace_snoc_step].
      §4  THE COUNTING CORE (O1/O2): the per-hart count of a prefix is the
          event's po position ([tpo_count]) and the per-log count is its
          [gwix] minus one ([tw_count]) — the po arm and the gmo|W arm of
          [ptrace_ext], each turned into a numeric identity — and the
          induction they carry.
      §5  THE THEOREM [gtrace_linearization].  RULE 14 IS NOT NEEDED: see
          the note there.
      §6  NON-VACUITY: the rank trace IS a [ptrace_ext] of every rule-14
          consistent graph ([glin_ptrace_ext]), so T2-1c′ SUBSUMES T2-1c
          ([rule14_linearization'] re-derives it), and the hypotheses are
          satisfiable at a real graph ([mpg']).
      §7  THE DEV-ORDER VERSION: [gfexec_consistent'] (the revised axiom:
          po ∪ rf ∪ gmo|W ∪ dev acyclic), the existence of a trace that is
          both a [ptrace_ext] and [tr_dev_ordered], and the composition
          with [WeakRvwmoFab.fconf_supply] ([fconf_trace_realize]).

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoLin.
Require Import WeakRvwmoTopo.
Require Import WeakSrvwmoLitmus.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. PLUMBING *)

Lemma before_index {A} (L : list A) (x y : A) m n :
  NoDup L → L !! m = Some x → L !! n = Some y → before L x y → (m < n)%nat.
Proof.
  intros Hnd Hm Hn (i & j & Hi & Hj & Hij).
  rewrite (NoDup_lookup L i m x Hnd Hi Hm) in Hij.
  by rewrite (NoDup_lookup L j n y Hnd Hj Hn) in Hij.
Qed.

Lemma elem_of_take_lookup {A} (l : list A) k (x : A) :
  x ∈ take k l ↔ ∃ p, (p < k)%nat ∧ l !! p = Some x.
Proof.
  split.
  - intros [p Hp]%elem_of_list_lookup.
    apply lookup_take_Some in Hp as [Hp Hlt]. by exists p.
  - intros (p & Hlt & Hp). apply elem_of_list_lookup.
    exists p. by apply lookup_take_Some.
Qed.

Lemma filter_all {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  (∀ x, x ∈ l → P x) → filter P l = l.
Proof.
  induction l as [|a l IH]; [done|]. intros Hall.
  rewrite (filter_cons_True P a l (Hall a ltac:(by left))).
  f_equal. apply IH. intros x Hx. apply Hall. by right.
Qed.

(** The count of a decidable class in a prefix jumps by one exactly at a
    member, and never decreases. *)
Lemma filter_take_S {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) p x :
  l !! p = Some x → P x →
  length (filter P (take (S p) l)) = S (length (filter P (take p l))).
Proof.
  intros Hp Hx. rewrite (take_S_r l p x Hp) list_basics.filter_app
    (filter_cons_True P x [] Hx) filter_nil length_app /=. lia.
Qed.

Lemma filter_take_mono' {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) k k' :
  (k ≤ k')%nat →
  (length (filter P (take k l)) ≤ length (filter P (take k' l)))%nat.
Proof.
  intros Hle.
  rewrite -(take_drop k (take k' l)) list_basics.filter_app length_app
    take_take (Nat.min_l k k' Hle). lia.
Qed.

(** The element of a list at the position its own prefix-count names. *)
Lemma filter_lookup_count {A} (P : A → Prop) `{∀ x, Decision (P x)}
    (l : list A) p x :
  l !! p = Some x → P x →
  filter P l !! length (filter P (take p l)) = Some x.
Proof.
  intros Hp Hx.
  have Hsplit : filter P l = filter P (take p l) ++ filter P (drop p l).
  { by rewrite -list_basics.filter_app take_drop. }
  rewrite Hsplit (drop_S l x p Hp) (filter_cons_True P x _ Hx).
  by apply list_lookup_middle.
Qed.

(* ====================================================================== *)
(** * 2. THE ORDER A TRACE MUST RESPECT *)

(** po ∪ rf ∪ gmo|W. *)
Definition ptrace_rel (G : gexec) (x y : geid) : Prop :=
  gpo G x y ∨ grf G x y ∨
  (gis_w G x = true ∧ gis_w G y = true ∧ gmo_lt G x y).

(** A TRACE: every program event once (fences included), in an order that
    extends [ptrace_rel]. *)
Definition ptrace_ext (G : gexec) (L : list geid) : Prop :=
  L ≡ₚ gevs' G ∧ ∀ x y, ptrace_rel G x y → before L x y.

(** The candidate a trace names: [G]'s labels, at [G]'s image. *)
Definition cand_of (G : gexec) (L : list geid) : cand :=
  Cand (gx_img G) (glin_step G <$> L).

Global Instance gmo_lt_dec2 G e1 e2 : Decision (gmo_lt G e1 e2).
Proof. rewrite /gmo_lt. apply _. Defined.

Lemma cand_of_tr G L : cd_tr (cand_of G L) = glin_step G <$> L.
Proof. done. Qed.

(** [gcnt] over a trace built from event ids IS the per-hart count of the
    ids. *)
Lemma gcnt_fmap G i (l : list geid) :
  gcnt i (glin_step G <$> l) = length (filter (λ x : geid, x.1 = i) l).
Proof.
  induction l as [|x l IH]; [done|].
  rewrite fmap_cons /gcnt filter_cons filter_cons.
  case_decide as H1; case_decide as H2; rewrite /gcnt in IH; simpl.
  - by rewrite IH.
  - by destruct (H2 H1).
  - by destruct (H1 H2).
  - exact IH.
Qed.

(* ====================================================================== *)
(** * 3. THE STEP: one snoc lemma over all four labels

    [WeakRvwmoFloor] §8 lands the read step (O3) and the write step (O4);
    the fence step (O5) is [WeakRvwmoCert.snoc_fence_consistent] plus the
    generic [gtrace_prefix_snoc].  WHAT IS NEW HERE IS THE RMW (O6): its
    read half is the read step verbatim (the floor induction of Floor §6
    already covers [LRmw] on both sides), and its [WeakAxiomatic.rmw_latest]
    obligation — "the appended RMW names the LATEST message of every byte"
    — is [gatomicity] read through the log dictionary:

      a message ABOVE the source in the log is, by [gtp_log_writes], a
      [gwrites] entry [w'] at its own [gwix]; the log's length is
      [gwix] of the RMW minus one ([gtp_wix], i.e. the gmo|W arm), so
      that message sits strictly between the source and the RMW's own
      write in gmo — which is exactly what [gatomicity] forbids.

    No ordering argument over the trace is needed: the whole content is
    the identification of log indices with [gwix], which §2's [tw_count]
    supplies for EVERY [ptrace_ext] trace. *)

(** [WeakRvwmoSupply.tcnt] and [WeakRvwmoFloor.gcnt] are the same count. *)
Lemma tcnt_gcnt i tr : tcnt i tr = gcnt i tr.
Proof. done. Qed.

(** A read footprint's value list matches its timestamp list, at any label
    that has one. *)
Lemma glb_rd_len G e l base ts vs :
  gwf G → gx_lbl G e = Some l → lb_rd l = Some (base, ts, vs) →
  length vs = length ts.
Proof.
  intros Hwf Hl Hrd. destruct l; simplify_eq/=.
  - exact (gshape G Hwf e _ Hl).
  - destruct (gshape G Hwf e _ Hl) as (_ & _ & H). exact H.
Qed.

(** [gtrace_prefix] reads [ev] only inside the trace. *)
Lemma gtrace_prefix_ev G c ev ev' :
  (∀ p s, cd_tr c !! p = Some s → ev p = ev' p) →
  gtrace_prefix G c ev → gtrace_prefix G c ev'.
Proof.
  intros Heq [Himg Hag Hpos Hlbl Hwix Hlog]. split.
  - exact Himg.
  - intros p s Hs. rewrite -(Heq p s Hs). by apply Hag.
  - intros p s Hs. rewrite -(Heq p s Hs). by apply Hpos.
  - intros p s Hs. rewrite -(Heq p s Hs). by apply Hlbl.
  - intros p s Hs Hw. rewrite -(Heq p s Hs). exact (Hwix p s Hs Hw).
  - exact Hlog.
Qed.

(** The read-admissibility of an appended read half, at whatever label
    carries it. *)
Lemma gtrace_snoc_rd_adm G c ev (i : agent) l base ts vs :
  rvwmo_minus_consistent G →
  gtrace_prefix G c ev →
  gx_lbl G (i, gcnt i (cd_tr c)) = Some l →
  lb_rd l = Some (base, ts, vs) →
  length vs = length ts →
  (∀ (j : nat) t, ts !! j = Some t → (t ≤ length (cd_log_end c))%nat) →
  snoc_rd_adm c i (lb_aq l) base ts vs.
Proof.
  intros Hcons Hgt Hl Hrd Hlen Hsrc.
  have Hce : cd_log_end c = cd_log c (length (cd_tr c)) := eq_refl.
  destruct Hcons as (Hwf & Hppo & Hlv & Hat).
  have Hrb : ∀ (j : nat) t v, ts !! j = Some t → vs !! j = Some v →
    greads_byte G (i, gcnt i (cd_tr c)) (acc_addr base j) t v.
  { intros j t v Hj Hv. by exists l, base, ts, vs, j. }
  split_and!.
  - exact Hlen.
  - intros j t v Hj Hv.
    pose proof (proj1 (Hlv _ _ _ _ (Hrb j t v Hj Hv))) as Hval.
    destruct t as [|n].
    + rewrite /log_byte. destruct Hgt as [Himg _ _ _ _ _]. by rewrite Himg.
    + destruct Hval as (w & Hw & Hwb & _).
      rewrite Hce.
      apply (gtp_log_byte G c ev Hgt (S n) w (acc_addr base j) v);
        [lia| |exact Hw|exact Hwb].
      rewrite -Hce. by eapply Hsrc.
  - intros j t Hj.
    apply (floor_of_graph G c ev i (i, gcnt i (cd_tr c)) (acc_addr base j) t
             (default (bv_0 8) (vs !! j)) (lb_aq l));
      [by split_and!|exact Hgt|done| |].
    + destruct (lookup_lt_is_Some_2 vs j
                  ltac:(rewrite Hlen; by eapply lookup_lt_Some)) as [v Hv].
      rewrite Hv /=. by apply Hrb.
    + intros Haq. by exists l.
Qed.

(** (O6) THE ATOMICITY CLAUSE. *)
Lemma gtrace_rmw_latest G c ev (i : agent) l base ts vs :
  rvwmo_minus_consistent G →
  gtrace_prefix G c ev →
  gx_lbl G (i, gcnt i (cd_tr c)) = Some l →
  lb_rd l = Some (base, ts, vs) →
  lb_is_w l = true →
  length vs = length ts →
  gwix G (i, gcnt i (cd_tr c)) = S (length (cd_log_end c)) →
  (∀ (j : nat) t, ts !! j = Some t → (t ≤ length (cd_log_end c))%nat) →
  ∀ (j : nat) t, ts !! j = Some t →
    latest (cd_img c) (cd_log_end c) (acc_addr base j) t.
Proof.
  intros Hcons Hgt Hl Hrd Hw Hlen Hix Hsrc j t Hj.
  pose proof Hcons as (Hwf & Hppo & Hlv & Hat).
  destruct (lookup_lt_is_Some_2 vs j
              ltac:(rewrite Hlen; by eapply lookup_lt_Some)) as [v Hv].
  have Hrb : greads_byte G (i, gcnt i (cd_tr c)) (acc_addr base j) t v
    by (exists l, base, ts, vs, j).
  split.
  - destruct (gtrace_snoc_rd_adm G c ev i l base ts vs Hcons Hgt Hl Hrd Hlen
                Hsrc) as (_ & Hval & _).
    rewrite (Hval j t v Hj Hv). by eexists.
  - intros (s & Hlo & Hhi & m & Hm & Hby).
    destruct (gtp_log_writes G c ev Hgt s m ltac:(lia) Hm (acc_addr base j) Hby)
      as (w' & v' & Hw' & Hwb').
    have Hix' : gwix G w' = s
      := proj2 (gwrite_at_inv G s w' (proj1 Hwf) Hw').
    apply (Hat (i, gcnt i (cd_tr c)) (acc_addr base j) t v Hrb
             ltac:(by exists l) w' v' Hwb').
    rewrite Hix' Hix. lia.
Qed.

(** THE SNOC STEP, at any label. *)
Theorem gtrace_snoc_step G c ev (i : agent) l :
  rvwmo_minus_consistent G →
  srvwmo_consistent c →
  gtrace_prefix G c ev →
  gx_lbl G (i, gcnt i (cd_tr c)) = Some l →
  (lb_is_w l = true →
     gwix G (i, gcnt i (cd_tr c)) = S (length (cd_log_end c))) →
  (∀ base ts vs, lb_rd l = Some (base, ts, vs) →
     ∀ (j : nat) t, ts !! j = Some t → (t ≤ length (cd_log_end c))%nat) →
  srvwmo_consistent (cand_snoc c (EStep i l)) ∧
  gtrace_prefix G (cand_snoc c (EStep i l))
    (ev_snoc c ev (i, gcnt i (cd_tr c))).
Proof.
  intros Hcons Hc Hgt Hl Hix Hsrc.
  destruct l as [aq base ts vs|rl base vs kc|pr pw sr sw|
                 aq rl base ts rvs wvs kc].
  - apply (gtrace_snoc_read_consistent G c ev i aq base ts vs Hcons Hc Hgt Hl).
    intros j t Hj. by eapply (Hsrc base ts vs eq_refl).
  - exact (gtrace_snoc_write_consistent G c ev i rl base vs kc (proj1 Hcons)
             Hc Hgt Hl (Hix eq_refl)).
  - split.
    + by apply snoc_fence_consistent.
    + eapply gtrace_prefix_snoc; [apply Hcons|exact Hgt|exact Hl|].
      intros Hcontra. discriminate.
  - split; last first.
    { eapply gtrace_prefix_snoc;
        [apply Hcons|exact Hgt|exact Hl|intros _; exact (Hix eq_refl)]. }
    destruct (gshape G (proj1 Hcons) _ _ Hl) as (Hne & Hlenw & Hlenr).
    eapply snoc_rmw_consistent; [exact Hc|exact Hne|exact Hlenw| |].
    + exact (gtrace_snoc_rd_adm G c ev i
               (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc) base ts rvs
               Hcons Hgt Hl eq_refl Hlenr
               (Hsrc base ts rvs eq_refl)).
    + exact (gtrace_rmw_latest G c ev i
               (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc) base ts rvs
               Hcons Hgt Hl eq_refl eq_refl Hlenr (Hix eq_refl)
               (Hsrc base ts rvs eq_refl)).
Qed.

(* ====================================================================== *)
(** * 4. THE COUNTING CORE (O1/O2) AND THE INDUCTION

    Everything below is at a FIXED graph and trace.  §4.1 is the po arm of
    [ptrace_ext] as a numeric identity ("the per-hart count of a prefix is
    the event's po position"), §4.2 the gmo|W arm ("the per-log count is
    [gwix] minus one"), §4.3 the log a prefix carries, §4.4 the induction
    itself, §4.5 the rows and the full log. *)
Section Trace.
  Context (G : gexec) (L : list geid).
  Hypothesis Hcons : rvwmo_minus_consistent G.
  Hypothesis Hext  : ptrace_ext G L.

  Local Lemma twf : gwf G.
  Proof. apply Hcons. Qed.
  Local Lemma tnd : NoDup L.
  Proof. rewrite (proj1 Hext). apply gevs_nodup. Qed.
  Local Lemma tmem e : e ∈ L ↔ is_Some (gx_lbl G e).
  Proof. rewrite (proj1 Hext). apply elem_of_gevs. Qed.

  Local Lemma tlbl k e : L !! k = Some e → is_Some (gx_lbl G e).
  Proof. intros Hk. apply tmem. by eapply elem_of_list_lookup_2. Qed.

  Local Lemma tord m n x y :
    L !! m = Some x → L !! n = Some y → ptrace_rel G x y → (m < n)%nat.
  Proof.
    intros Hm Hn HR. eapply before_index; [apply tnd|exact Hm|exact Hn|].
    by apply (proj2 Hext).
  Qed.

  Local Lemma tnodup_take k : NoDup (take k L).
  Proof.
    pose proof tnd as Hnd. rewrite -(take_drop k L) in Hnd.
    by destruct (proj1 (list_relations.NoDup_app _ _) Hnd) as (H & _ & _).
  Qed.

  (* -------------------------------------------------------------- *)
  (** ** 4.1 THE po ARM: the per-hart prefix count is the po position *)

  Local Lemma tpo_perm k e :
    L !! k = Some e →
    filter (λ x : geid, x.1 = e.1) (take k L)
      ≡ₚ (λ j, (e.1, j)) <$> seq 0 e.2.
  Proof.
    intros Hk.
    have Hel : is_Some (gx_lbl G e) := tlbl k e Hk.
    have Hb : (e.1 < length (gx_prog G))%nat ∧ (e.2 < length (grow G e.1))%nat
      := proj1 (gx_lbl_bounds G e) Hel.
    apply list_relations.NoDup_Permutation.
    - by apply list_relations.NoDup_filter, tnodup_take.
    - apply NoDup_fmap_2; [intros a b [= Hb']; exact Hb'|apply NoDup_seq].
    - intros x. rewrite elem_of_list_filter elem_of_take_lookup
        elem_of_list_fmap. split.
      + intros (Hx1 & p & Hlt & Hp).
        have Hxl : is_Some (gx_lbl G x) := tlbl p x Hp.
        exists x.2. split; [by destruct x; simplify_eq/=|].
        apply elem_of_seq. split; [lia|]. simpl.
        destruct (decide (x.2 < e.2)%nat) as [?|Hge]; [lia|exfalso].
        destruct (decide (x.2 = e.2)) as [Heq|Hne].
        * have Hxe : x = e by (destruct x, e; simplify_eq/=).
          subst x. rewrite (NoDup_lookup L p k e tnd Hp Hk) in Hlt. lia.
        * have Hpo : gpo G e x
            by (split_and!; [by rewrite Hx1|lia|exact Hel|exact Hxl]).
          pose proof (tord k p e x Hk Hp (or_introl Hpo)). lia.
      + intros (j & -> & Hj%elem_of_seq). simpl. split; [done|].
        have Hjb : (j < length (grow G e.1))%nat by lia.
        have Hjl : is_Some (gx_lbl G (e.1, j)).
        { apply gx_lbl_bounds. simpl. split; [apply Hb|exact Hjb]. }
        destruct (elem_of_list_lookup_1 L (e.1, j) (proj2 (tmem _) Hjl))
          as [p Hp].
        exists p. split; [|exact Hp].
        have Hpo : gpo G (e.1, j) e
          by (split_and!; simpl; [done|lia|exact Hjl|exact Hel]).
        by eapply (tord p k _ e Hp Hk (or_introl Hpo)).
  Qed.

  Local Lemma tpo_count k e :
    L !! k = Some e →
    gcnt e.1 (cd_tr (cand_of G (take k L))) = e.2.
  Proof.
    intros Hk. rewrite cand_of_tr gcnt_fmap
      (length_Permutation_proper _ _ (tpo_perm k e Hk)) length_fmap
      length_seq //.
  Qed.

  (* -------------------------------------------------------------- *)
  (** ** 4.2 THE gmo|W ARM: the log count is [gwix] minus one *)

  Local Lemma twrites_mem x :
    x ∈ gwrites G ↔ x ∈ L ∧ gis_w G x = true.
  Proof.
    split.
    - intros Hx. split;
        [apply tmem; exact (gwrites_lbl G twf x Hx)|by apply gwrites_isw].
    - intros [Hx Hw]. by apply gis_w_gwrites; [apply twf|apply tmem|].
  Qed.

  (** The writes of a prefix are exactly the writes gmo-before the event at
      its end — the gmo|W arm and the totality of gmo. *)
  Local Lemma tw_perm k e :
    L !! k = Some e → gis_w G e = true →
    filter (λ x : geid, gis_w G x) (take k L)
      ≡ₚ filter (λ w, gmo_lt G w e) (gwrites G).
  Proof.
    intros Hk Hw.
    have Hnd : NoDup (gx_gmo G) := proj1 twf.
    have He : e ∈ gwrites G by (apply twrites_mem; split;
      [by eapply elem_of_list_lookup_2|done]).
    apply list_relations.NoDup_Permutation.
    - by apply list_relations.NoDup_filter, tnodup_take.
    - by apply list_relations.NoDup_filter, gwrites_nodup.
    - intros x.
      rewrite (elem_of_list_filter (λ y : geid, gis_w G y) (take k L) x)
              (elem_of_list_filter (λ w : geid, gmo_lt G w e) (gwrites G) x)
              elem_of_take_lookup. split.
      + intros (Hxw & p & Hlt & Hp).
        apply Is_true_true_1 in Hxw.
        have Hx : x ∈ gwrites G by (apply twrites_mem; split;
          [by eapply elem_of_list_lookup_2|done]).
        split; [|exact Hx].
        have Hne : x ≠ e.
        { intros Heq. rewrite Heq in Hp.
          rewrite (NoDup_lookup L p k e tnd Hp Hk) in Hlt. lia. }
        destruct (gmo_lt_total G x e Hnd
                    (proj1 (proj1 (gwrites_elem_of G x) Hx))
                    (proj1 (proj1 (gwrites_elem_of G e) He)) Hne) as [Hmo|Hmo];
          [exact Hmo|exfalso].
        pose proof (tord k p e x Hk Hp
          (or_intror (or_intror (conj Hw (conj Hxw Hmo))))). lia.
      + intros (Hmo & Hx).
        have Hxw : gis_w G x = true by apply gwrites_isw.
        split; [by apply Is_true_true_2|].
        destruct (elem_of_list_lookup_1 L x (proj1 (proj1 (twrites_mem x) Hx)))
          as [p Hp].
        exists p. split; [|exact Hp].
        by eapply (tord p k x e Hp Hk
          (or_intror (or_intror (conj Hxw (conj Hw Hmo))))).
  Qed.

  (** … and there are exactly [gwix e - 1] of those. *)
  Local Lemma tw_below n e :
    gwrites G !! n = Some e →
    filter (λ w, gmo_lt G w e) (gwrites G) = take n (gwrites G).
  Proof.
    intros Hn.
    have Hnd : NoDup (gx_gmo G) := proj1 twf.
    have Hss := gwrites_sorted G Hnd.
    have Hem : e ∈ gwrites G by eapply elem_of_list_lookup_2.
    rewrite -{1}(take_drop n (gwrites G)) list_basics.filter_app
      (drop_S _ e n Hn).
    have H1 : filter (λ w, gmo_lt G w e) (take n (gwrites G))
            = take n (gwrites G).
    { apply filter_all. intros x [p [Hp Hlt]%lookup_take_Some]%elem_of_list_lookup.
      have Hx : x ∈ gwrites G by eapply elem_of_list_lookup_2.
      split_and!; [by apply gwrites_elem_of|by apply gwrites_elem_of|].
      by apply (StronglySorted_lookup_elim _ _ p n x e Hss Hp Hn). }
    have H2 : filter (λ w, gmo_lt G w e) (e :: drop (S n) (gwrites G)) = [].
    { apply filter_no. intros x Hx (_ & _ & Hlt).
      apply elem_of_cons in Hx as [->|[p Hp]%elem_of_list_lookup]; [lia|].
      rewrite lookup_drop in Hp.
      have Hgt := StronglySorted_lookup_elim _ _ n (S n + p)%nat e x Hss Hn Hp
        ltac:(lia). lia. }
    rewrite H1 H2 app_nil_r //.
  Qed.

  Local Lemma tw_count k e :
    L !! k = Some e → gis_w G e = true →
    gwix G e = S (length (filter (λ x : geid, gis_w G x) (take k L))).
  Proof.
    intros Hk Hw.
    have Hnd : NoDup (gx_gmo G) := proj1 twf.
    have He : e ∈ gwrites G by (apply twrites_mem; split;
      [by eapply elem_of_list_lookup_2|done]).
    destruct (gwix_lookup G e He) as (n & Hn & Hix).
    rewrite Hix (length_Permutation_proper _ _ (tw_perm k e Hk Hw))
      (tw_below n e Hn) length_take.
    apply lookup_lt_Some in Hn. lia.
  Qed.

  (** THE WRITE LIST: a trace's writes, in trace order, ARE [gwrites]. *)
  Local Lemma tw_list : filter (λ x : geid, gis_w G x) L = gwrites G.
  Proof.
    have Hnd : NoDup (gx_gmo G) := proj1 twf.
    have Hperm : filter (λ x : geid, gis_w G x) L ≡ₚ gwrites G.
    { apply list_relations.NoDup_Permutation.
      - by apply list_relations.NoDup_filter, tnd.
      - by apply gwrites_nodup.
      - intros x.
        rewrite (elem_of_list_filter (λ y : geid, gis_w G y) L x) twrites_mem.
        split; [intros [H1 H2]; split; [exact H2|by apply Is_true_true_1]|].
        intros [H1 H2]; split; [by apply Is_true_true_2|exact H1]. }
    apply list_eq. intros n.
    destruct (gwrites G !! n) as [w|] eqn:Hw; last first.
    { apply lookup_ge_None. apply lookup_ge_None in Hw.
      rewrite (length_Permutation_proper _ _ Hperm). exact Hw. }
    have Hwm : w ∈ gwrites G by eapply elem_of_list_lookup_2.
    have Hwb : gis_w G w = true by apply gwrites_isw.
    destruct (elem_of_list_lookup_1 L w (proj1 (proj1 (twrites_mem w) Hwm)))
      as [p Hp].
    pose proof (tw_count p w Hp Hwb) as Hc.
    rewrite (gwix_of_lookup G n w Hnd Hw) in Hc.
    have Hn : n = length (filter (λ x : geid, gis_w G x) (take p L)) by lia.
    rewrite Hn. apply filter_lookup_count; [exact Hp|by apply Is_true_true_2].
  Qed.

  (* -------------------------------------------------------------- *)
  (** ** 4.3 THE LOG OF A PREFIX *)

  Local Lemma tlog_end k :
    cd_log_end (cand_of G (take k L)) = omap (gmsg G) (take k L).
  Proof.
    rewrite cd_log_end_full cand_of_tr tr_msgs_omap omap_glin //.
  Qed.

  Local Lemma tlog_len k :
    length (cd_log_end (cand_of G (take k L)))
      = length (filter (λ x : geid, gis_w G x) (take k L)).
  Proof. rewrite tlog_end omap_gmsg_len //. Qed.

  (** (O2) A READ'S SOURCE IS ALREADY IN THE LOG — the rf arm. *)
  Local Lemma tsrc_bound k e a t v :
    L !! k = Some e → greads_byte G e a t v →
    (t ≤ length (cd_log_end (cand_of G (take k L))))%nat.
  Proof.
    intros Hk Hrd. rewrite tlog_len.
    destruct t as [|n]; [lia|].
    destruct Hcons as (Hwf & _ & Hlv & _).
    destruct (proj1 (Hlv e a (S n) v Hrd)) as (w & Hw & _ & _).
    have Hrf : grf G w e by (exists a, (S n), v).
    destruct (gwrite_at_inv G (S n) w (proj1 Hwf) Hw) as (Hwm & Hix).
    have Hwb : gis_w G w = true by apply gwrites_isw.
    destruct (elem_of_list_lookup_1 L w (proj1 (proj1 (twrites_mem w) Hwm)))
      as [p Hp].
    have Hlt : (p < k)%nat := tord p k w e Hp Hk (or_intror (or_introl Hrf)).
    rewrite -Hix (tw_count p w Hp Hwb)
      -(filter_take_S (λ x : geid, gis_w G x) L p w Hp
          ltac:(by apply Is_true_true_2)).
    apply filter_take_mono'. lia.
  Qed.

  (* -------------------------------------------------------------- *)
  (** ** 4.4 THE INDUCTION (O1): every prefix is a G-trace prefix *)

  Local Definition tev : nat → geid := λ p, default (0%nat, 0%nat) (L !! p).

  Local Lemma tisw e : is_Some (gx_lbl G e) → lb_is_w (glbl G e) = gis_w G e.
  Proof. intros [l Hl]. by rewrite /glbl /gis_w Hl. Qed.

  Local Lemma tcand_len k :
    (k ≤ length L)%nat → length (cd_tr (cand_of G (take k L))) = k.
  Proof. intros Hk. rewrite cand_of_tr length_fmap length_take. lia. Qed.

  Local Lemma tprefix k :
    srvwmo_consistent (cand_of G (take k L)) ∧
    gtrace_prefix G (cand_of G (take k L)) tev.
  Proof.
    induction k as [|k IH].
    - have Ht0 : cd_tr (cand_of G (take 0 L)) = [] by done.
      split.
      + apply srvwmo_of_wf, cand_reachable. intros kk s Hs.
        rewrite Ht0 in Hs. by destruct kk.
      + split.
        * done.
        * intros p s Hs. rewrite Ht0 in Hs. by destruct p.
        * intros p s Hs. rewrite Ht0 in Hs. by destruct p.
        * intros p s Hs. rewrite Ht0 in Hs. by destruct p.
        * intros p s Hs. rewrite Ht0 in Hs. by destruct p.
        * intros s Hs Hle. rewrite /cd_log Ht0 /= in Hle. lia.
    - destruct (L !! k) as [e|] eqn:Hk; last first.
      { apply lookup_ge_None in Hk.
        have Hge : take (S k) L = take k L.
        { transitivity L; [apply take_ge; lia|symmetry; apply take_ge; lia]. }
        rewrite Hge. exact IH. }
      have Hlt : (k < length L)%nat := lookup_lt_Some L k e Hk.
      have Hcl : length (cd_tr (cand_of G (take k L))) = k
        := tcand_len k ltac:(lia).
      have Hel : is_Some (gx_lbl G e) := tlbl k e Hk.
      have Hcnt : gcnt e.1 (cd_tr (cand_of G (take k L))) = e.2
        := tpo_count k e Hk.
      have Hev : (e.1, gcnt e.1 (cd_tr (cand_of G (take k L)))) = e.
      { rewrite Hcnt. by destruct e. }
      have Hl : gx_lbl G (e.1, gcnt e.1 (cd_tr (cand_of G (take k L))))
              = Some (glbl G e).
      { rewrite Hev. destruct Hel as [l Hl]. by rewrite /glbl Hl. }
      have Hsnoc : cand_snoc (cand_of G (take k L)) (EStep e.1 (glbl G e))
                 = cand_of G (take (S k) L).
      { rewrite /cand_snoc /cand_of /= (take_S_r L k e Hk) fmap_app //. }
      have Hix : lb_is_w (glbl G e) = true →
        gwix G (e.1, gcnt e.1 (cd_tr (cand_of G (take k L))))
          = S (length (cd_log_end (cand_of G (take k L)))).
      { intros Hw. rewrite Hev tlog_len (tw_count k e Hk) //.
        by rewrite -(tisw e Hel). }
      have Hsrcb : ∀ base ts vs, lb_rd (glbl G e) = Some (base, ts, vs) →
        ∀ (j : nat) t, ts !! j = Some t →
          (t ≤ length (cd_log_end (cand_of G (take k L))))%nat.
      { intros base ts vs Hrd j t Hj.
        destruct Hel as [l Hl'].
        have Hgl : glbl G e = l by rewrite /glbl Hl'.
        rewrite Hgl in Hrd.
        have Hlen := glb_rd_len G e l base ts vs twf Hl' Hrd.
        destruct (lookup_lt_is_Some_2 vs j
                    ltac:(rewrite Hlen; by eapply lookup_lt_Some)) as [v Hv].
        apply (tsrc_bound k e (acc_addr base j) t v Hk).
        by exists l, base, ts, vs, j. }
      destruct (gtrace_snoc_step G (cand_of G (take k L)) tev e.1 (glbl G e)
                  Hcons (proj1 IH) (proj2 IH) Hl Hix Hsrcb) as [Hc' Hp'].
      rewrite Hsnoc in Hc'. rewrite Hsnoc in Hp'.
      split; [exact Hc'|].
      eapply gtrace_prefix_ev; [|exact Hp'].
      intros p s Hs.
      have Hplt : (p < S k)%nat.
      { pose proof (lookup_lt_Some _ _ _ Hs) as Hb.
        rewrite (tcand_len (S k) ltac:(lia)) in Hb. lia. }
      destruct (decide (p < k)%nat) as [Hp|Hp].
      + rewrite (ev_snoc_lt (cand_of G (take k L)) tev _ p ltac:(lia)) //.
      + have Hpk : p = k by lia.
        subst p.
        have Hnk : ¬ (k < length (cd_tr (cand_of G (take k L))))%nat by lia.
        rewrite /ev_snoc (bool_decide_eq_false_2 _ Hnk) /tev Hk /=.
        exact Hev.
  Qed.

  (* -------------------------------------------------------------- *)
  (** ** 4.5 THE ROWS AND THE LOG *)

  Local Lemma thart_len i :
    length (filter (λ x : geid, x.1 = i) L) = length (grow G i).
  Proof.
    have Hperm : filter (λ x : geid, x.1 = i) L ≡ₚ gevs_hart G i.
    { apply list_relations.NoDup_Permutation.
      - by apply list_relations.NoDup_filter, tnd.
      - apply gevs_hart_nodup.
      - intros x. rewrite (elem_of_list_filter (λ y : geid, y.1 = i) L x)
          elem_of_gevs_hart tmem. split.
        + intros [H1 H2]. split; [exact H1|].
          rewrite -H1. by apply (proj1 (gx_lbl_bounds G x) H2).
        + intros [H1 H2]. split; [exact H1|].
          apply gx_lbl_bounds. rewrite H1. split; [|exact H2].
          destruct (gx_prog G !! i) as [row|] eqn:Hp;
            [by eapply lookup_lt_Some|].
          exfalso. rewrite /grow Hp /= in H2. lia. }
    rewrite (length_Permutation_proper _ _ Hperm) /gevs_hart length_fmap
      length_seq //.
  Qed.

  Local Lemma trow_eq i : trow i (cd_tr (cand_of G L)) = grow G i.
  Proof.
    have Hlen : length (trow i (cd_tr (cand_of G L))) = length (grow G i).
    { have Hg : gcnt i (cd_tr (cand_of G L)) = length (grow G i).
      { rewrite cand_of_tr gcnt_fmap thart_len //. }
      rewrite /trow length_fmap. exact Hg. }
    apply list_eq. intros n.
    destruct (decide (n < length (grow G i))%nat) as [Hn|Hn]; last first.
    { have H1 : trow i (cd_tr (cand_of G L)) !! n = None
        by (apply lookup_ge_None_2; lia).
      have H2 : grow G i !! n = None by (apply lookup_ge_None_2; lia).
      rewrite H1 H2 //. }
    have Hi : (i < length (gx_prog G))%nat.
    { destruct (gx_prog G !! i) as [row|] eqn:Hp; [by eapply lookup_lt_Some|].
      exfalso. rewrite /grow Hp /= in Hn. lia. }
    have Hlbl : is_Some (gx_lbl G (i, n)) by (apply gx_lbl_bounds; by split).
    destruct (elem_of_list_lookup_1 L (i, n) (proj2 (tmem _) Hlbl)) as [p Hp].
    have Hs : cd_tr (cand_of G L) !! p = Some (glin_step G (i, n)).
    { rewrite cand_of_tr list_lookup_fmap Hp //. }
    pose proof (trow_at i (cd_tr (cand_of G L)) p (glin_step G (i, n)) Hs
                  eq_refl) as Hrow.
    have Htk : take p (cd_tr (cand_of G L)) = cd_tr (cand_of G (take p L)).
    { rewrite !cand_of_tr fmap_take //. }
    rewrite Htk tcnt_gcnt (tpo_count p (i, n) Hp) /= in Hrow.
    rewrite Hrow. symmetry.
    destruct Hlbl as [l Hl]. rewrite /glbl Hl /=.
    rewrite /gx_lbl /grow /= in Hl |- *.
    destruct (gx_prog G !! i) as [row|]; [exact Hl|done].
  Qed.

  Local Lemma tlog_full :
    cd_log (cand_of G L) (length (cd_tr (cand_of G L)))
      = omap (gmsg G) (gwrites G).
  Proof.
    have Hge : take (length (cd_tr (cand_of G L))) (cd_tr (cand_of G L))
             = cd_tr (cand_of G L) by (apply take_ge; lia).
    rewrite /cd_log Hge cand_of_tr tr_msgs_omap omap_glin.
    rewrite (omap_gmsg_filter G L) tw_list //.
  Qed.

  Local Lemma tfull :
    srvwmo_consistent (cand_of G L) ∧
    gtrace_prefix G (cand_of G L) tev.
  Proof.
    have Hge : take (length L) L = L by (apply take_ge; lia).
    pose proof (tprefix (length L)) as H. by rewrite Hge in H.
  Qed.
End Trace.

(* ====================================================================== *)
(** * 5. THE THEOREM

    RULE 14 IS NOT A HYPOTHESIS.  [WeakRvwmoLin.rule14_linearization] needs
    it to BUILD its trace (the rank blocks); here the trace is given, and
    the gmo|W arm of [ptrace_ext] is strictly stronger than rule 14 on the
    write–write pairs that matter: a graph with a write po-before a write
    but gmo-after it admits no [ptrace_ext] trace at all (po demands one
    order, gmo|W the other).  So [gtrace_linearization_min] takes only
    [rvwmo_minus_consistent], and [gtrace_linearization] is its restatement
    in the shape that REPLACES T2-1c. *)

Theorem gtrace_linearization_min G L :
  rvwmo_minus_consistent G → ptrace_ext G L →
  srvwmo_consistent (cand_of G L) ∧
  cd_img (cand_of G L) = gx_img G ∧
  (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr (cand_of G L))
        = default [] (gx_prog G !! i)) ∧
  cd_log (cand_of G L) (length (cd_tr (cand_of G L)))
    = omap (gmsg G) (gwrites G).
Proof.
  intros Hcons Hext. split_and!.
  - exact (proj1 (tfull G L Hcons Hext)).
  - done.
  - exact (trow_eq G L Hext).
  - exact (tlog_full G L Hcons Hext).
Qed.

Theorem gtrace_linearization G L :
  rvwmo_minus_consistent G → grule14 G → ptrace_ext G L →
  srvwmo_consistent (cand_of G L) ∧
  cd_img (cand_of G L) = gx_img G ∧
  (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr (cand_of G L))
        = default [] (gx_prog G !! i)) ∧
  cd_log (cand_of G L) (length (cd_tr (cand_of G L)))
    = omap (gmsg G) (gwrites G).
Proof. intros Hcons _ Hext. by apply gtrace_linearization_min. Qed.

(* ====================================================================== *)
(** * 6. T2-1c′ SUBSUMES T2-1c, AND NON-VACUITY

    The RANK trace of [WeakRvwmoLin] is one [ptrace_ext] of every rule-14
    consistent graph.  Two of the three arms are new here:

      - rf: [w →rf r] gives [gmo_lt w r], and the rank of [r] is the [gwix]
        of [r]'s NEXT po-write [u] (or a past-the-end slot).  Rule 14 turns
        [r →po u] into [gmo_lt r u], hence [gmo_lt w u] and
        [gwix w < gwix u] — so the ranks are STRICTLY ordered and the rf
        edge crosses a block boundary.  THIS is where rule 14 is needed:
        not by T2-1c′ itself (§4), but by the CONSTRUCTION of this trace.
      - gmo|W: on writes the rank IS [gwix] ([grank_write]).

    The po arm is [WeakRvwmoLin.glin_po_lt] (inside a block the order is po
    order).  Consequently [rule14_linearization'] re-derives T2-1c from
    T2-1c′, and the hypotheses of §4 are jointly satisfiable at a real
    three-event graph ([mpg'], §5.2). *)

Section Rank.
  Context (G : gexec).
  Hypothesis Hcons : rvwmo_minus_consistent G.
  Hypothesis H14 : grule14 G.

  Local Lemma rwf : gwf G.
  Proof. apply Hcons. Qed.

  Local Lemma rgmem e : e ∈ gx_gmo G → is_Some (gx_lbl G e).
  Proof.
    intros He. destruct (proj1 ((proj1 (proj2 rwf)) e) He) as (l & Hl & _).
    by exists l.
  Qed.

  (** A strictly larger rank is a strictly later block. *)
  Local Lemma rk_before x y :
    is_Some (gx_lbl G x) → is_Some (gx_lbl G y) →
    (grank G x < grank G y)%nat → before (glin_eids G) x y.
  Proof.
    intros Hx Hy Hlt.
    destruct (glin_index G rwf x Hx) as [kx Hkx].
    destruct (glin_index G rwf y Hy) as [ky Hky].
    exists kx, ky. split_and!; [exact Hkx|exact Hky|].
    destruct (decide (kx < ky)%nat) as [?|Hge]; [done|exfalso].
    destruct (decide (kx = ky)) as [Heq|Hne].
    { rewrite Heq Hky in Hkx. simplify_eq. lia. }
    have Hle := StronglySorted_lookup_elim _ _ ky kx y x
                  (rblocks_rank_sorted (grank G) (gevs G) (grank_bound G))
                  Hky Hkx ltac:(lia).
    cbn in Hle. lia.
  Qed.

  (** A write gmo-before an event has a strictly smaller rank. *)
  Local Lemma rk_gmo_w w e :
    w ∈ gwrites G → gmo_lt G w e → (grank G w < grank G e)%nat.
  Proof.
    intros Hw Hmo.
    have Hnd : NoDup (gx_gmo G) := proj1 rwf.
    destruct e as [i k].
    have Hel : is_Some (gx_lbl G (i, k)) := rgmem _ (proj1 (proj2 Hmo)).
    have Hb := proj1 (gx_lbl_bounds G (i, k)) Hel.
    destruct Hb as [Hbi Hbk]. simpl in Hbi, Hbk.
    rewrite (grank_write G rwf w Hw) /grank.
    destruct (gnxw G (i, k)) as [u|] eqn:Hf.
    - destruct (gnxw_Some G i k u Hf) as (m & -> & Hkm & Hm & Hwm & _).
      have Hlm : is_Some (gx_lbl G (i, m)) := glbl_some G i m Hbi Hm.
      have Hum : (i, m) ∈ gwrites G := gis_w_gwrites G (i, m) rwf Hlm Hwm.
      have Hmo' : gmo_lt G w (i, m).
      { destruct (decide (k = m)) as [Heq|Hne]; [by rewrite -Heq|].
        eapply gmo_lt_trans; [exact Hmo|].
        apply H14.
        - split_and!; simpl; [done|lia|exact Hel|exact Hlm].
        - exact (proj1 ((proj1 (proj2 rwf)) (i, k)) (proj1 (proj2 Hmo))).
        - exact (gis_w_glbl_is G (i, m) Hlm Hwm). }
      apply (proj2 (gwix_gpos_lt G w (i, m) Hnd Hw Hum)).
      exact (proj2 (proj2 Hmo')).
    - have Hle := gwix_le G w Hw. simpl. lia.
  Qed.

  Local Lemma rk_po x y : gpo G x y → before (glin_eids G) x y.
  Proof.
    intros (Hag & Hlt & Hx & Hy).
    destruct (glin_index G rwf x Hx) as [kx Hkx].
    destruct (glin_index G rwf y Hy) as [ky Hky].
    exists kx, ky. split_and!; [exact Hkx|exact Hky|].
    exact (glin_po_lt G rwf H14 kx ky x y Hkx Hky Hag Hlt).
  Qed.

  Local Lemma rk_rf w r : grf G w r → before (glin_eids G) w r.
  Proof.
    intros (a & t & v & Hrd & Hw).
    destruct t as [|n]; [done|].
    have Hnd : NoDup (gx_gmo G) := proj1 rwf.
    destruct (gwrite_at_inv G (S n) w Hnd Hw) as [Hwm _].
    have Hmo : gmo_lt G w r
      := grf_gmo G (proj1 (proj2 Hcons)) (proj1 (proj2 (proj2 Hcons)))
           r a n v w Hrd Hw.
    apply rk_before.
    - exact (gwrites_lbl G rwf w Hwm).
    - exact (rgmem r (proj1 (proj2 Hmo))).
    - by apply rk_gmo_w.
  Qed.

  Local Lemma rk_ww x y :
    gis_w G x = true → gis_w G y = true → gmo_lt G x y →
    before (glin_eids G) x y.
  Proof.
    intros Hx Hy Hmo.
    have Hlx : is_Some (gx_lbl G x) := rgmem x (proj1 Hmo).
    have Hly : is_Some (gx_lbl G y) := rgmem y (proj1 (proj2 Hmo)).
    apply rk_before; [exact Hlx|exact Hly|].
    apply rk_gmo_w; [exact (gis_w_gwrites G x rwf Hlx Hx)|exact Hmo].
  Qed.

  Theorem glin_ptrace_ext : ptrace_ext G (glin_eids G).
  Proof.
    split.
    - apply rblocks_perm; [apply gevs_nodup|].
      intros x Hx. apply (grank_lt_bound G rwf). by apply elem_of_gevs.
    - intros x y [Hpo|[Hrf|(Hx & Hy & Hmo)]];
        [by apply rk_po|by apply rk_rf|by apply rk_ww].
  Qed.
End Rank.

(** T2-1c, re-derived: the rank trace's candidate is exactly
    [WeakRvwmoLin.lin_cand]. *)
Corollary rule14_linearization' G :
  rvwmo_minus_consistent G → grule14 G →
  srvwmo_consistent (cand_of G (glin_eids G)) ∧
  cd_img (cand_of G (glin_eids G)) = gx_img G ∧
  (∀ i, (λ s, es_lb s) <$>
          filter (λ s, es_ag s = i) (cd_tr (cand_of G (glin_eids G)))
        = default [] (gx_prog G !! i)) ∧
  cd_log (cand_of G (glin_eids G))
         (length (cd_tr (cand_of G (glin_eids G))))
    = omap (gmsg G) (gwrites G).
Proof.
  intros Hcons H14. apply gtrace_linearization_min; [exact Hcons|].
  by apply glin_ptrace_ext.
Qed.

Lemma cand_of_lin_cand G : cand_of G (glin_eids G) = lin_cand G.
Proof. done. Qed.

(* ---------------------------------------------------------------------- *)
(** ** 6.2 NON-VACUITY at a real graph

    [WeakRvwmoProbeK1.mpg']: three events over two harts (hart 0 loads then
    stores; hart 1 stores), rule-14 and RVWMO⁻-consistent. *)
Require Import WeakRvwmoProbeK1.

Theorem gtrace_linearization_nonvacuous :
  ptrace_ext mpg' (glin_eids mpg') ∧
  srvwmo_consistent (cand_of mpg' (glin_eids mpg')) ∧
  length (cd_tr (cand_of mpg' (glin_eids mpg'))) = 3%nat.
Proof.
  have Hext : ptrace_ext mpg' (glin_eids mpg')
    := glin_ptrace_ext mpg' mpg'_consistent mpg'_rule14.
  split_and!; [exact Hext| |].
  - exact (proj1 (gtrace_linearization_min mpg' _ mpg'_consistent Hext)).
  - rewrite cand_of_tr length_fmap.
    rewrite (length_Permutation_proper _ _ (proj1 Hext)). done.
Qed.

(* ====================================================================== *)
(** * 7. THE DEV-ORDER VERSION

    B1b-2's finding (route-b §4d.4): [gdev_adj ⊆ gmo] is NOT the honest
    fabric axiom — a dev block's fabric time is its hart's PROGRAM-ORDER
    time, so a block hung on an early READ can be fabric-late, and there
    are rule-14 consistent graphs with [dev ⊆ gmo] that NO trace realizes.
    The honest axiom is that po ∪ rf ∪ gmo|W ∪ dev is ACYCLIC — literally
    "the fabric order is realizable by the machine's own ordering" — and
    that is [gfexec_consistent'] below.

    NEITHER AXIOM IMPLIES THE OTHER.  [gfexec_consistent] can hold with
    [gfexec_consistent'] failing (the counterexample just cited: dev ⊆ gmo
    but the union cyclic), and [gfexec_consistent'] can hold with
    [gfexec_consistent] failing (a dev edge between two reads, or from a
    read to a gmo-earlier write, is unconstrained by po ∪ rf ∪ gmo|W yet
    breaks [gdev_adj ⊆ gmo]).  For [gf_dev = []] both reduce to the graph
    axioms, and §6.1 records that. *)
Require Import WeakRvwmoDec.
Require Import WeakEvPf.
Require Import WeakEvInst.
Require Import WeakAxRealize.
Require Import WeakRvwmoFab.
Require Import WeakRvwmoFabInd.

Definition ptrace_relF (GF : gfexec) (x y : geid) : Prop :=
  ptrace_rel (gd_g (gf_gd GF)) x y ∨ gdev_adj GF x y.

Definition gfexec_consistent' (GF : gfexec) : Prop :=
  rvwmo_minus_deps_consistent (gf_gd GF) ∧
  (∀ x, ¬ tc (ptrace_relF GF) x x).

Global Instance ptrace_rel_dec G x y : Decision (ptrace_rel G x y).
Proof. rewrite /ptrace_rel. apply _. Defined.

Global Instance ptrace_relF_dec GF x y : Decision (ptrace_relF GF x y).
Proof. rewrite /ptrace_relF. apply _. Defined.

(* ---------------------------------------------------------------------- *)
(** ** 7.1 The two axioms *)

Lemma ptrace_ext_acyclic G L :
  ptrace_ext G L → ∀ x, ¬ tc (ptrace_rel G) x x.
Proof.
  intros Hext x Htc.
  have Hnd : NoDup L by (rewrite (proj1 Hext); apply gevs_nodup).
  have Hb : ∀ a b, tc (ptrace_rel G) a b → before L a b.
  { induction 1 as [a b HR|a u b HR _ IH];
      [by apply (proj2 Hext)|
       eapply before_trans; [exact Hnd|by apply (proj2 Hext)|exact IH]]. }
  destruct (Hb x x Htc) as (i & j & Hi & Hj & Hij).
  rewrite (NoDup_lookup L i j x Hnd Hi Hj) in Hij. lia.
Qed.

(** With no fabric the revised axiom is the graph's own rule-14
    consistency (through §5's rank trace), and the OLD axiom is free. *)
Lemma gfexec_consistent'_nodev GF :
  gf_dev GF = [] →
  rvwmo_minus_deps_consistent (gf_gd GF) →
  grule14 (gd_g (gf_gd GF)) →
  gfexec_consistent' GF.
Proof.
  intros Hnil Hc H14. split; [exact Hc|].
  have Hsub : ∀ x y, ptrace_relF GF x y → ptrace_rel (gd_g (gf_gd GF)) x y.
  { intros x y [H|(n & Hn & _)]; [exact H|]. by rewrite Hnil in Hn. }
  intros x Htc. eapply (ptrace_ext_acyclic _ _
    (glin_ptrace_ext (gd_g (gf_gd GF)) (proj1 Hc) H14) x).
  eapply tc_mono; [exact Hsub|exact Htc].
Qed.

Lemma gfexec_consistent_nodev GF :
  gf_dev GF = [] → rvwmo_minus_deps_consistent (gf_gd GF) →
  gfexec_consistent GF.
Proof.
  intros Hnil Hc. split; [exact Hc|].
  intros a b (n & Hn & _). by rewrite Hnil in Hn.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 7.2 EXISTENCE of a fabric-ordered trace *)

Lemma ptrace_rel_mem G x y :
  ptrace_rel G x y → is_Some (gx_lbl G x) ∧ is_Some (gx_lbl G y).
Proof.
  intros [(_ & _ & Hx & Hy)|[(a & t & v & Hrd & Hw)|(Hx & Hy & _)]].
  - by split.
  - split.
    + destruct t as [|n]; [done|].
      rewrite /gwrite_at in Hw.
      have Hwm : x ∈ gwrites G by eapply elem_of_list_lookup_2.
      apply gwrites_elem_of in Hwm as [Hwm Hwb].
      rewrite /gis_w in Hwb. by destruct (gx_lbl G x).
    + destruct Hrd as (l & _ & _ & _ & _ & Hl & _). by exists l.
  - rewrite /gis_w in Hx, Hy. split;
      [by destruct (gx_lbl G x)|by destruct (gx_lbl G y)].
Qed.

Theorem ptrace_exists_F (GF : gfexec) :
  gfexec_consistent' GF →
  (∀ e, e ∈ gf_dev GF → is_Some (gx_lbl (gd_g (gf_gd GF)) e)) →
  ∃ L, ptrace_ext (gd_g (gf_gd GF)) L ∧
       (∀ m n e e', (m < n)%nat →
          gf_dev GF !! m = Some e → gf_dev GF !! n = Some e' → before L e e').
Proof.
  intros [Hc Hacy] Hdev.
  destruct (topo_sort_exists (ptrace_relF GF) (λ x y, ptrace_relF_dec GF x y)
              Hacy (gevs' (gd_g (gf_gd GF))) (gevs_nodup _))
    as (L & HL & Hord).
  have Hmem : ∀ x y, ptrace_relF GF x y →
    x ∈ gevs' (gd_g (gf_gd GF)) ∧ y ∈ gevs' (gd_g (gf_gd GF)).
  { intros x y [HR|(n & Hn & Hsn)].
    - destruct (ptrace_rel_mem _ _ _ HR) as [Hx Hy].
      split; by apply elem_of_gevs'.
    - split; apply elem_of_gevs', Hdev; by eapply elem_of_list_lookup_2. }
  have Hbef : ∀ x y, ptrace_relF GF x y → before L x y.
  { intros x y HR. destruct (Hmem x y HR) as [Hx Hy]. by apply Hord. }
  have Hnd : NoDup L by (rewrite HL; apply gevs_nodup).
  exists L. split.
  - split; [exact HL|]. intros x y HR. apply Hbef. by left.
  - intros m n e e' Hlt Hm Hn.
    remember (n - S m)%nat as d eqn:Hd. revert m n e e' Hlt Hm Hn Hd.
    induction d as [|d IH]; intros m n e e' Hlt Hm Hn Hd.
    + have Heq : n = S m by lia. rewrite Heq in Hn.
      apply Hbef. right. by exists m.
    + destruct (lookup_lt_is_Some_2 (gf_dev GF) (S m)) as [e2 He2].
      { pose proof (lookup_lt_Some _ _ _ Hn). lia. }
      eapply before_trans; [exact Hnd| |].
      * apply Hbef. right. by exists m.
      * apply (IH (S m) n e2 e'); [lia|done|done|lia].
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 7.3 THE TRACE VISITS THE DEV BLOCKS IN [gf_dev]'s ORDER *)

(** A duplicate-free list whose elements a trace both CONTAINS and ORDERS
    occupies the trace in its own order: the trace-prefix count of [M]'s
    members below an element of [M] IS that element's index in [M].  This
    is [tw_list]'s argument for [gwrites], stated once and abstractly. *)
Lemma filter_ordered_count {A} `{EqDecision A} (L M : list A) n p x :
  NoDup L → NoDup M →
  (∀ y, y ∈ M → y ∈ L) →
  (∀ m m' y z, (m < m')%nat → M !! m = Some y → M !! m' = Some z →
     before L y z) →
  M !! n = Some x → L !! p = Some x →
  length (filter (λ y, y ∈ M) (take p L)) = n.
Proof.
  intros HndL HndM Hsub Hord Hn Hp.
  have Hcount : filter (λ y, y ∈ M) (take p L) ≡ₚ take n M.
  { apply list_relations.NoDup_Permutation.
    - apply list_relations.NoDup_filter.
      rewrite -(take_drop p L) in HndL.
      by destruct (proj1 (list_relations.NoDup_app _ _) HndL) as (H & _ & _).
    - rewrite -(take_drop n M) in HndM.
      by destruct (proj1 (list_relations.NoDup_app _ _) HndM) as (H & _ & _).
    - intros y. rewrite (elem_of_list_filter (λ z, z ∈ M) (take p L) y)
        elem_of_take_lookup elem_of_take_lookup. split.
      + intros (Hy & q & Hq & HqL).
        destruct (elem_of_list_lookup_1 M y Hy) as [m Hm].
        exists m. split; [|exact Hm].
        destruct (decide (m < n)%nat) as [?|Hge]; [done|exfalso].
        destruct (decide (m = n)) as [Heq|Hne].
        * rewrite Heq Hn in Hm. simplify_eq.
          rewrite (NoDup_lookup L q p y HndL HqL Hp) in Hq. lia.
        * have Hb := Hord n m x y ltac:(lia) Hn Hm.
          pose proof (before_index L x y p q HndL Hp HqL Hb). lia.
      + intros (m & Hmn & Hm).
        have HyM : y ∈ M by eapply elem_of_list_lookup_2.
        split; [exact HyM|].
        destruct (elem_of_list_lookup_1 L y (Hsub y HyM)) as [q Hq].
        exists q. split; [|exact Hq].
        have Hb := Hord m n y x Hmn Hm Hn.
        exact (before_index L y x q p HndL Hq Hp Hb). }
  rewrite (length_Permutation_proper _ _ Hcount) length_take.
  apply lookup_lt_Some in Hn. lia.
Qed.

Lemma dcnt_filter G L GF k :
  ptrace_ext G L →
  dcnt GF (cd_tr (cand_of G L)) k
    = length (filter (λ x : geid, x ∈ gf_dev GF) (take k L)).
Proof.
  intros Hext. induction k as [|k IH]; [done|].
  destruct (L !! k) as [e|] eqn:Hk; last first.
  { have Hnone : cd_tr (cand_of G L) !! k = None
      by (rewrite cand_of_tr list_lookup_fmap Hk //).
    have Hge : take (S k) L = take k L.
    { apply lookup_ge_None in Hk.
      transitivity L; [apply take_ge; lia|symmetry; apply take_ge; lia]. }
    rewrite Hge -IH (dcnt_step_ne GF _ k) //. by rewrite /dstep_at Hnone. }
  have Hs : cd_tr (cand_of G L) !! k = Some (glin_step G e)
    by (rewrite cand_of_tr list_lookup_fmap Hk //).
  have Htk : take k (cd_tr (cand_of G L)) = cd_tr (cand_of G (take k L))
    by (rewrite !cand_of_tr fmap_take //).
  have Hev : (es_ag (glin_step G e),
              tcnt (es_ag (glin_step G e)) (take k (cd_tr (cand_of G L)))) = e.
  { rewrite /glin_step /= Htk tcnt_gcnt (tpo_count G L Hext k e Hk).
    by destruct e. }
  rewrite (take_S_r L k e Hk) list_basics.filter_app.
  destruct (decide (e ∈ gf_dev GF)) as [Hin|Hin].
  - rewrite (dcnt_step_dev GF _ k); last first.
    { rewrite /dstep_at Hs Hev. by apply bool_decide_eq_true_2. }
    rewrite IH (filter_cons_True (λ x : geid, x ∈ gf_dev GF) e [] Hin)
      filter_nil length_app /=. lia.
  - rewrite (dcnt_step_ne GF _ k); last first.
    { rewrite /dstep_at Hs Hev. by apply bool_decide_eq_false_2. }
    rewrite IH (filter_cons_False (λ x : geid, x ∈ gf_dev GF) e [] Hin)
      app_nil_r //.
Qed.

Theorem tr_dev_ordered_of_ptrace (GF : gfexec) (L : list geid) :
  ptrace_ext (gd_g (gf_gd GF)) L →
  NoDup (gf_dev GF) →
  (∀ e, e ∈ gf_dev GF → is_Some (gx_lbl (gd_g (gf_gd GF)) e)) →
  (∀ m n e e', (m < n)%nat →
     gf_dev GF !! m = Some e → gf_dev GF !! n = Some e' → before L e e') →
  tr_dev_ordered GF (cand_of (gd_g (gf_gd GF)) L).
Proof.
  intros Hext Hnd Hlbl Hord.
  set G := gd_g (gf_gd GF).
  have HndL : NoDup L by (rewrite (proj1 Hext); apply gevs_nodup).
  have Hsub : ∀ y, y ∈ gf_dev GF → y ∈ L.
  { intros x Hx. apply (proj2 (tmem G L Hext x)). by apply Hlbl. }
  intros k s Hs Hin.
  destruct (L !! k) as [e|] eqn:Hk; last first.
  { exfalso. rewrite cand_of_tr list_lookup_fmap Hk /= in Hs. done. }
  have Hse : s = glin_step G e.
  { rewrite cand_of_tr list_lookup_fmap Hk /= in Hs. by simplify_eq. }
  have Htk : take k (cd_tr (cand_of G L)) = cd_tr (cand_of G (take k L))
    by (rewrite !cand_of_tr fmap_take //).
  have Hev : (es_ag s, tcnt (es_ag s) (take k (cd_tr (cand_of G L)))) = e.
  { rewrite Hse /glin_step /= Htk tcnt_gcnt (tpo_count G L Hext k e Hk).
    by destruct e. }
  rewrite Hev. rewrite Hev in Hin.
  destruct (elem_of_list_lookup_1 (gf_dev GF) e Hin) as [n Hn].
  rewrite (dcnt_filter G L GF k Hext)
    (filter_ordered_count L (gf_dev GF) n k e HndL Hnd Hsub Hord Hn Hk).
  exact Hn.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** 7.4 THE COMPOSITION: [fconf_supply]'s missing hypothesis, supplied *)

Theorem fconf_supply' (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) (GF : gfexec) (N : nat) (L : list geid) :
  gfexec_conf boot d0 fab GF →
  rvwmo_minus_consistent (gd_g (gf_gd GF)) →
  ptrace_ext (gd_g (gf_gd GF)) L →
  (∀ m n e e', (m < n)%nat →
     gf_dev GF !! m = Some e → gf_dev GF !! n = Some e' → before L e e') →
  (length (gx_prog (gd_g (gf_gd GF))) ≤ N)%nat →
  ∃ pst : nat → list pexv6,
    pst 0%nat = boot <$> seq 0 N ∧
    fab (dcnt GF (cd_tr (cand_of (gd_g (gf_gd GF)) L)) 0%nat) = d0 ∧
    exec_prog_ok' pstep_ev pcls_ev pst
      (λ k, fab (dcnt GF (cd_tr (cand_of (gd_g (gf_gd GF)) L)) k))
      (cand_exec (cand_of (gd_g (gf_gd GF)) L)).
Proof.
  intros Hconf Hcons Hext Hord HN.
  apply (fconf_supply (cand_of (gd_g (gf_gd GF)) L) boot d0 fab GF N Hconf).
  - exact (trow_eq (gd_g (gf_gd GF)) L Hext).
  - exact HN.
  - apply tr_dev_ordered_of_ptrace; [exact Hext| | |exact Hord].
    + apply Hconf.
    + intros e He.
      destruct (elem_of_list_lookup_1 (gf_dev GF) e He) as [n Hn].
      destruct e as [i k].
      destruct Hconf as (_ & _ & Hpos & _).
      destruct (Hpos n i k Hn) as (row & Hrow & Hlt).
      rewrite /gx_lbl /= Hrow /=. by apply lookup_lt_is_Some_2.
Qed.

(** THE DELIVERABLE: from the REVISED axiom alone, a linearization that is
    simultaneously sRVWMO-consistent and fabric-ordered. *)
Theorem fconf_trace_realize (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) (GF : gfexec) (N : nat) :
  gfexec_consistent' GF →
  gfexec_conf boot d0 fab GF →
  (length (gx_prog (gd_g (gf_gd GF))) ≤ N)%nat →
  ∃ (L : list geid) (pst : nat → list pexv6),
    let c := cand_of (gd_g (gf_gd GF)) L in
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g (gf_gd GF)) ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = default [] (gx_prog (gd_g (gf_gd GF)) !! i)) ∧
    cd_log c (length (cd_tr c))
      = omap (gmsg (gd_g (gf_gd GF))) (gwrites (gd_g (gf_gd GF))) ∧
    pst 0%nat = boot <$> seq 0 N ∧
    fab (dcnt GF (cd_tr c) 0%nat) = d0 ∧
    exec_prog_ok' pstep_ev pcls_ev pst (λ k, fab (dcnt GF (cd_tr c) k))
      (cand_exec c).
Proof.
  intros Hc' Hconf HN.
  have Hcons : rvwmo_minus_consistent (gd_g (gf_gd GF)) := proj1 (proj1 Hc').
  have Hlbl : ∀ e, e ∈ gf_dev GF → is_Some (gx_lbl (gd_g (gf_gd GF)) e).
  { intros e He.
    destruct (elem_of_list_lookup_1 (gf_dev GF) e He) as [n Hn].
    destruct e as [i k].
    destruct Hconf as (_ & _ & Hpos & _).
    destruct (Hpos n i k Hn) as (row & Hrow & Hlt).
    rewrite /gx_lbl /= Hrow /=. by apply lookup_lt_is_Some_2. }
  destruct (ptrace_exists_F GF Hc' Hlbl) as (L & Hext & Hord).
  destruct (fconf_supply' boot d0 fab GF N L Hconf Hcons Hext Hord HN)
    as (pst & Hp0 & Hd0 & Hok).
  destruct (gtrace_linearization_min (gd_g (gf_gd GF)) L Hcons Hext)
    as (H1 & H2 & H3 & H4).
  exists L, pst. split_and!; assumption.
Qed.

(* ====================================================================== *)
(** * 8. AUDIT *)

Print Assumptions gtrace_snoc_step.
Print Assumptions gtrace_linearization_min.
Print Assumptions gtrace_linearization.
Print Assumptions glin_ptrace_ext.
Print Assumptions rule14_linearization'.
Print Assumptions gtrace_linearization_nonvacuous.
Print Assumptions ptrace_exists_F.
Print Assumptions tr_dev_ordered_of_ptrace.
Print Assumptions fconf_supply'.
Print Assumptions fconf_trace_realize.
